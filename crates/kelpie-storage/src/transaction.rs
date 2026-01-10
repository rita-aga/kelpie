//! Transaction support for KV operations
//!
//! TigerStyle: Explicit transaction lifecycle, bounded operations.

use kelpie_core::Result;

/// Transaction state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransactionState {
    /// Transaction is active
    Active,
    /// Transaction has been committed
    Committed,
    /// Transaction has been aborted
    Aborted,
}

/// A transaction for atomic KV operations
///
/// Transactions provide all-or-nothing semantics for a batch of KV operations.
pub struct Transaction {
    /// Unique transaction ID
    pub id: u64,
    /// Current state
    pub state: TransactionState,
    /// Operations in this transaction
    operations: Vec<TransactionOp>,
}

/// Operation within a transaction
#[derive(Debug, Clone)]
pub enum TransactionOp {
    Set { key: Vec<u8>, value: Vec<u8> },
    Delete { key: Vec<u8> },
}

impl Transaction {
    /// Create a new transaction
    pub fn new(id: u64) -> Self {
        Self {
            id,
            state: TransactionState::Active,
            operations: Vec::new(),
        }
    }

    /// Add a set operation
    pub fn set(&mut self, key: Vec<u8>, value: Vec<u8>) -> Result<()> {
        debug_assert_eq!(self.state, TransactionState::Active);
        self.operations.push(TransactionOp::Set { key, value });
        Ok(())
    }

    /// Add a delete operation
    pub fn delete(&mut self, key: Vec<u8>) -> Result<()> {
        debug_assert_eq!(self.state, TransactionState::Active);
        self.operations.push(TransactionOp::Delete { key });
        Ok(())
    }

    /// Get the operations in this transaction
    pub fn operations(&self) -> &[TransactionOp] {
        &self.operations
    }

    /// Mark transaction as committed
    pub fn commit(&mut self) {
        debug_assert_eq!(self.state, TransactionState::Active);
        self.state = TransactionState::Committed;
    }

    /// Mark transaction as aborted
    pub fn abort(&mut self) {
        debug_assert_eq!(self.state, TransactionState::Active);
        self.state = TransactionState::Aborted;
    }
}
