//! The IronDict protocol on top of DeepFold and the Index STARK

pub mod audit;
pub mod consistency;
pub mod epoch;
pub mod lookup;
pub mod opening;
pub mod registration;
pub mod state;
pub mod update;

pub use audit::{AuditEvidence, VerifiedHistory, verify_history, verify_range};
pub use consistency::{ConsistencyProof, VerifiedConsistency, verify_consistency};
pub use epoch::{
    RecurrenceProof, TransitionProof, VerifiedTransition, prove_transition, verify_transition,
};
pub use lookup::{
    LookupProof, PlacementPath, VerifiedLookup, VerifiedLookupResult, VerifiedPlacement,
    verify_lookup, verify_placement,
};
pub use state::{
    CommittedStatePolynomial, Entry, EpochSnapshot, EpochTimings, PublicEpoch, ServerState,
    StateCommitments, StatePolynomial,
};
