// Copyright 2024 TiKV Project Authors. Licensed under Apache-2.0.

//! Trace validation tests for raft-rs.
//!
//! Generates ndjson execution traces from randomized Raft scenarios and
//! validates them against the formal Raft safety invariants using the TLC
//! model checker. See `tla-trace-validation/` for the TLA+ specs and runner.
//!
//! Methodology follows "Smart Casual Verification of the Confidential
//! Consortium Framework" (NSDI'25).

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::PathBuf;

use harness::*;
use raft::eraftpb::*;
use raft::storage::MemStorage;
use raft::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::{json, Value as JsonValue};

mod test_util;

fn trace_dir() -> PathBuf {
    let dir = PathBuf::from(
        std::env::var("RAFT_TRACE_DIR")
            .unwrap_or_else(|_| "tla-trace-validation/traces".to_string()),
    );
    fs::create_dir_all(&dir).unwrap();
    dir
}

// ---------------------------------------------------------------------------
// State capture
// ---------------------------------------------------------------------------

fn capture_node_state(raft: &Raft<MemStorage>, servers: &[u64]) -> JsonValue {
    let log_entries: Vec<JsonValue> = raft
        .raft_log
        .all_entries()
        .iter()
        .map(|e| json!({"term": e.term, "value": format!("v{}", e.index)}))
        .collect();

    let state_str = match raft.state {
        StateRole::Follower => "Follower",
        StateRole::Candidate | StateRole::PreCandidate => "Candidate",
        StateRole::Leader => "Leader",
    };

    let mut next_index = HashMap::new();
    let mut match_index = HashMap::new();
    for &s in servers {
        if let Some(pr) = raft.prs().get(s) {
            next_index.insert(s.to_string(), pr.next_idx);
            match_index.insert(s.to_string(), pr.matched);
        } else {
            next_index.insert(s.to_string(), 1u64);
            match_index.insert(s.to_string(), 0u64);
        }
    }

    let votes_granted: Vec<u64> = raft
        .prs()
        .votes()
        .iter()
        .filter_map(|(&id, &granted)| if granted { Some(id) } else { None })
        .collect();

    json!({
        "id": raft.id,
        "currentTerm": raft.term,
        "state": state_str,
        "votedFor": raft.vote,
        "log": log_entries,
        "commitIndex": raft.raft_log.committed,
        "persisted": raft.raft_log.persisted,
        "applied": raft.raft_log.applied,
        "leaderId": raft.leader_id,
        "nextIndex": next_index,
        "matchIndex": match_index,
        "votesGranted": votes_granted,
    })
}

fn capture_cluster_state(network: &Network, servers: &[u64]) -> JsonValue {
    let mut states = HashMap::new();
    for &id in servers {
        if let Some(peer) = network.peers.get(&id) {
            if let Some(ref raft) = peer.raft {
                states.insert(id.to_string(), capture_node_state(raft, servers));
            }
        }
    }
    json!(states)
}

fn capture_message(msg: &Message) -> JsonValue {
    let mtype = match msg.get_msg_type() {
        MessageType::MsgRequestVote | MessageType::MsgRequestPreVote => "RequestVoteRequest",
        MessageType::MsgRequestVoteResponse | MessageType::MsgRequestPreVoteResponse => {
            "RequestVoteResponse"
        }
        MessageType::MsgAppend | MessageType::MsgHeartbeat => "AppendEntriesRequest",
        MessageType::MsgAppendResponse | MessageType::MsgHeartbeatResponse => {
            "AppendEntriesResponse"
        }
        _ => "Other",
    };

    let entries: Vec<JsonValue> = msg
        .entries
        .iter()
        .map(|e| json!({"term": e.term, "value": format!("v{}", e.index)}))
        .collect();

    match mtype {
        "RequestVoteRequest" => json!({
            "mtype": mtype, "mterm": msg.term,
            "mlastLogTerm": msg.log_term, "mlastLogIndex": msg.index,
            "msource": msg.from, "mdest": msg.to,
        }),
        "RequestVoteResponse" => json!({
            "mtype": mtype, "mterm": msg.term,
            "mvoteGranted": !msg.reject,
            "msource": msg.from, "mdest": msg.to,
        }),
        "AppendEntriesRequest" => json!({
            "mtype": mtype, "mterm": msg.term,
            "mprevLogIndex": msg.index, "mprevLogTerm": msg.log_term,
            "mentries": entries, "mcommitIndex": msg.commit,
            "msource": msg.from, "mdest": msg.to,
        }),
        "AppendEntriesResponse" => json!({
            "mtype": mtype, "mterm": msg.term,
            "msuccess": !msg.reject, "mmatchIndex": msg.index,
            "msource": msg.from, "mdest": msg.to,
        }),
        _ => json!({
            "mtype": mtype, "mterm": msg.term,
            "msource": msg.from, "mdest": msg.to,
        }),
    }
}

// ---------------------------------------------------------------------------
// Tracing network wrapper
// ---------------------------------------------------------------------------

/// Wraps the test [`Network`] to emit an ndjson trace of every action.
struct TracingNetwork {
    network: Network,
    servers: Vec<u64>,
    trace_file: fs::File,
    step: u64,
}

impl TracingNetwork {
    fn new(n: usize, config: &Config, logger: &slog::Logger, path: &str) -> Self {
        let peers: Vec<Option<Interface>> = (0..n).map(|_| None).collect();
        let network = Network::new_with_config(peers, config, logger);
        let servers: Vec<u64> = (1..=n as u64).collect();
        let trace_file = fs::File::create(path).unwrap();

        let mut tn = TracingNetwork {
            network,
            servers,
            trace_file,
            step: 0,
        };
        let state = capture_cluster_state(&tn.network, &tn.servers);
        tn.emit("Init", 0, None, None, &state);
        tn
    }

    fn emit(
        &mut self,
        action: &str,
        node: u64,
        target: Option<u64>,
        message: Option<&Message>,
        cluster_state: &JsonValue,
    ) {
        let mut line = json!({
            "tag": "raft_trace",
            "step": self.step,
            "action": action,
            "node": node,
            "state": cluster_state,
        });
        if let Some(t) = target {
            line["target"] = json!(t);
        }
        if let Some(msg) = message {
            line["message"] = capture_message(msg);
        }
        writeln!(self.trace_file, "{}", serde_json::to_string(&line).unwrap()).unwrap();
        self.step += 1;
    }

    /// Emit AppendEntries events decomposed to at most 1 entry each,
    /// matching raft.tla's step granularity.
    fn emit_ae_decomposed(
        &mut self,
        action: &str,
        msg: &Message,
        cluster_state: &JsonValue,
    ) {
        let n_entries = msg.entries.len();
        if n_entries <= 1 {
            self.emit(action, msg.from, Some(msg.to), Some(msg), cluster_state);
            return;
        }
        // Decompose: emit one event per entry with incrementing prevLogIndex.
        let base_prev = msg.index; // mprevLogIndex for the first entry
        for k in 0..n_entries {
            let entry = &msg.entries[k];
            let prev_idx = base_prev + k as u64;
            let prev_term = if k == 0 {
                msg.log_term
            } else {
                msg.entries[k - 1].term
            };
            let single_msg = json!({
                "mtype": "AppendEntriesRequest",
                "mterm": msg.term,
                "mprevLogIndex": prev_idx,
                "mprevLogTerm": prev_term,
                "mentries": [{"term": entry.term, "value": format!("v{}", entry.index)}],
                "mcommitIndex": msg.commit,
                "msource": msg.from,
                "mdest": msg.to,
            });
            let mut line = json!({
                "tag": "raft_trace",
                "step": self.step,
                "action": action,
                "node": msg.from,
                "target": msg.to,
                "state": cluster_state,
                "message": single_msg,
            });
            writeln!(self.trace_file, "{}", serde_json::to_string(&line).unwrap()).unwrap();
            self.step += 1;
        }
    }

    fn timeout(&mut self, id: u64) {
        let state = capture_cluster_state(&self.network, &self.servers);
        self.emit("Timeout", id, None, None, &state);

        let mut msg = Message::default();
        msg.set_msg_type(MessageType::MsgHup);
        msg.to = id;
        msg.from = id;
        let peer = self.network.peers.get_mut(&id).unwrap();
        let _ = peer.step(msg);
        peer.persist();
        let msgs: Vec<Message> = peer.read_messages();

        for m in self.network.filter(msgs.iter().cloned()) {
            if matches!(
                m.get_msg_type(),
                MessageType::MsgRequestVote | MessageType::MsgRequestPreVote
            ) {
                let state = capture_cluster_state(&self.network, &self.servers);
                self.emit("RequestVote", m.from, Some(m.to), Some(&m), &state);
            }
        }
        self.deliver_messages(msgs);
    }

    fn deliver_messages(&mut self, msgs: Vec<Message>) {
        let mut pending = self.network.filter(msgs);
        while !pending.is_empty() {
            let mut new_msgs = vec![];
            for m in pending.drain(..) {
                let action = match m.get_msg_type() {
                    MessageType::MsgRequestVote | MessageType::MsgRequestPreVote => {
                        "HandleRequestVoteRequest"
                    }
                    MessageType::MsgRequestVoteResponse
                    | MessageType::MsgRequestPreVoteResponse => "HandleRequestVoteResponse",
                    MessageType::MsgAppend | MessageType::MsgHeartbeat => {
                        "HandleAppendEntriesRequest"
                    }
                    MessageType::MsgAppendResponse | MessageType::MsgHeartbeatResponse => {
                        "HandleAppendEntriesResponse"
                    }
                    _ => "HandleOther",
                };

                let receiver_term = self
                    .network
                    .peers
                    .get(&m.to)
                    .and_then(|p| p.raft.as_ref().map(|r| r.term))
                    .unwrap_or(0);
                if m.term > receiver_term {
                    let state = capture_cluster_state(&self.network, &self.servers);
                    self.emit("UpdateTerm", m.to, Some(m.from), Some(&m), &state);
                }

                let resp = {
                    let p = self.network.peers.get_mut(&m.to).unwrap();
                    let _ = p.step(m.clone());
                    p.persist();
                    p.read_messages()
                };

                let state = capture_cluster_state(&self.network, &self.servers);
                if action == "HandleAppendEntriesRequest" && m.entries.len() > 1 {
                    // Decompose multi-entry AE receive into individual single-entry events.
                    let base_prev = m.index;
                    for k in 0..m.entries.len() {
                        let entry = &m.entries[k];
                        let prev_idx = base_prev + k as u64;
                        let prev_term = if k == 0 {
                            m.log_term
                        } else {
                            m.entries[k - 1].term
                        };
                        let single_msg = json!({
                            "mtype": "AppendEntriesRequest",
                            "mterm": m.term,
                            "mprevLogIndex": prev_idx,
                            "mprevLogTerm": prev_term,
                            "mentries": [{"term": entry.term, "value": format!("v{}", entry.index)}],
                            "mcommitIndex": m.commit,
                            "msource": m.from,
                            "mdest": m.to,
                        });
                        let mut line = json!({
                            "tag": "raft_trace",
                            "step": self.step,
                            "action": action,
                            "node": m.to,
                            "target": m.from,
                            "state": &state,
                            "message": single_msg,
                        });
                        writeln!(self.trace_file, "{}", serde_json::to_string(&line).unwrap()).unwrap();
                        self.step += 1;
                    }
                } else {
                    self.emit(action, m.to, Some(m.from), Some(&m), &state);
                }

                if action == "HandleRequestVoteResponse" {
                    let is_leader = self
                        .network
                        .peers
                        .get(&m.to)
                        .and_then(|p| p.raft.as_ref())
                        .map_or(false, |r| r.state == StateRole::Leader);
                    if is_leader {
                        let state = capture_cluster_state(&self.network, &self.servers);
                        self.emit("BecomeLeader", m.to, None, None, &state);
                    }
                }

                let filtered_resp = self.network.filter(resp);

                for rm in &filtered_resp {
                    match rm.get_msg_type() {
                        MessageType::MsgRequestVote | MessageType::MsgRequestPreVote => {
                            let state = capture_cluster_state(&self.network, &self.servers);
                            self.emit("RequestVote", rm.from, Some(rm.to), Some(rm), &state);
                        }
                        MessageType::MsgAppend | MessageType::MsgHeartbeat => {
                            let state = capture_cluster_state(&self.network, &self.servers);
                            self.emit_ae_decomposed("AppendEntries", rm, &state);
                        }
                        _ => {}
                    };
                }

                new_msgs.extend(filtered_resp);
            }
            pending.append(&mut new_msgs);
        }
    }

    fn client_request(&mut self, leader_id: u64) {
        let value = format!("v{}", self.step);

        let state = capture_cluster_state(&self.network, &self.servers);
        let mut line = json!({
            "tag": "raft_trace",
            "step": self.step,
            "action": "ClientRequest",
            "node": leader_id,
            "state": state,
            "value": &value,
        });
        writeln!(self.trace_file, "{}", serde_json::to_string(&line).unwrap()).unwrap();
        self.step += 1;

        let mut msg = Message::default();
        msg.set_msg_type(MessageType::MsgPropose);
        msg.from = leader_id;
        msg.to = leader_id;
        let mut entry = Entry::default();
        entry.data = value.into_bytes().into();
        msg.entries = vec![entry].into();

        let peer = self.network.peers.get_mut(&leader_id).unwrap();
        let _ = peer.step(msg);
        peer.persist();

        let state = capture_cluster_state(&self.network, &self.servers);
        self.emit("AdvanceCommitIndex", leader_id, None, None, &state);

        let msgs: Vec<Message> = self
            .network
            .peers
            .get_mut(&leader_id)
            .unwrap()
            .read_messages();

        // Only emit AE sends for messages that will actually be delivered.
        for m in self.network.filter(msgs.iter().cloned()) {
            if matches!(
                m.get_msg_type(),
                MessageType::MsgAppend | MessageType::MsgHeartbeat
            ) {
                let state = capture_cluster_state(&self.network, &self.servers);
                self.emit_ae_decomposed("AppendEntries", &m, &state);
            }
        }
        self.deliver_messages(msgs);
    }

    fn isolate(&mut self, id: u64) {
        let state = capture_cluster_state(&self.network, &self.servers);
        self.emit("DropMessage", id, None, None, &state);
        self.network.isolate(id);
    }

    fn recover(&mut self) {
        let state = capture_cluster_state(&self.network, &self.servers);
        self.emit("RecoverNetwork", 0, None, None, &state);
        self.network.recover();
    }

    fn find_leader(&self) -> Option<u64> {
        self.servers.iter().copied().find(|&id| {
            self.network
                .peers
                .get(&id)
                .and_then(|p| p.raft.as_ref())
                .map_or(false, |r| r.state == StateRole::Leader)
        })
    }

    fn flush(&mut self) {
        self.trace_file.flush().unwrap();
    }
}

// ---------------------------------------------------------------------------
// Randomized scenario driver
// ---------------------------------------------------------------------------

fn run_randomized_scenario(
    seed: u64,
    n_nodes: usize,
    n_ops: usize,
    config: &Config,
    trace_path: &str,
) {
    let logger = raft::default_logger();
    let mut tn = TracingNetwork::new(n_nodes, config, &logger, trace_path);
    let mut rng = StdRng::seed_from_u64(seed);

    // Initial election.
    tn.timeout(rng.gen_range(1..=n_nodes as u64));

    for _ in 0..n_ops {
        match rng.gen_range(0u32..100) {
            0..=34 => {
                if let Some(leader) = tn.find_leader() {
                    tn.client_request(leader);
                }
            }
            35..=49 => {
                tn.timeout(rng.gen_range(1..=n_nodes as u64));
            }
            50..=59 => {
                tn.isolate(rng.gen_range(1..=n_nodes as u64));
            }
            60..=69 => {
                tn.recover();
            }
            70..=79 => {
                // Partition leader, elect a replacement, then heal.
                if let Some(leader) = tn.find_leader() {
                    tn.isolate(leader);
                    tn.timeout(rng.gen_range(1..=n_nodes as u64));
                    if let Some(new_leader) = tn.find_leader() {
                        tn.client_request(new_leader);
                    }
                    tn.recover();
                }
            }
            80..=89 => {
                // Burst proposals.
                if let Some(leader) = tn.find_leader() {
                    for _ in 0..rng.gen_range(2u32..6) {
                        tn.client_request(leader);
                    }
                }
            }
            90..=99 => {
                // Competing elections.
                let a = rng.gen_range(1..=n_nodes as u64);
                tn.timeout(a);
                let b = rng.gen_range(1..=n_nodes as u64);
                if b != a {
                    tn.timeout(b);
                }
            }
            _ => {}
        }
    }
    tn.flush();
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn test_trace_generation_3node() {
    let dir = trace_dir();
    let config = Network::default_config();

    for seed in 0..10 {
        let path = dir.join(format!("rand3n_{seed}.ndjson"));
        run_randomized_scenario(seed, 3, 50, &config, path.to_str().unwrap());
        let lines = fs::read_to_string(&path).unwrap().lines().count();
        assert!(lines > 10, "seed {seed}: trace too short ({lines} lines)");
    }
}

#[test]
fn test_trace_generation_5node() {
    let dir = trace_dir();
    let config = Network::default_config();

    for seed in 0..10 {
        let path = dir.join(format!("rand5n_{seed}.ndjson"));
        run_randomized_scenario(seed, 5, 50, &config, path.to_str().unwrap());
        let lines = fs::read_to_string(&path).unwrap().lines().count();
        assert!(lines > 10, "seed {seed}: trace too short ({lines} lines)");
    }
}

#[test]
fn test_trace_generation_prevote_check_quorum() {
    let dir = trace_dir();
    let mut config = Network::default_config();
    config.pre_vote = true;
    config.check_quorum = true;

    for seed in 0..10 {
        let path = dir.join(format!("prevote_cq_{seed}.ndjson"));
        run_randomized_scenario(seed, 5, 50, &config, path.to_str().unwrap());
        let lines = fs::read_to_string(&path).unwrap().lines().count();
        assert!(lines > 10, "seed {seed}: trace too short ({lines} lines)");
    }
}
