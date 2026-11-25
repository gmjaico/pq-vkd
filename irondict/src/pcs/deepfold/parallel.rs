use std::sync::Arc;

use rayon::{ThreadPool, ThreadPoolBuilder};

use crate::{Error, Result};

// thread/worker pool for Deepfold prover work, verification work
// done by users never uses this as they run single threaded

#[derive(Clone)]
pub struct ProverConfig {
    threads: usize,
    pool: Arc<ThreadPool>,
    sequential_pool: Arc<ThreadPool>,
}

impl ProverConfig {
    pub fn new(threads: usize) -> Result<Self> {
        if threads == 0 {
            return Err(Error::InvalidParameters(
                "prover worker count must be at least one",
            ));
        }
        let pool = Arc::new(
            ThreadPoolBuilder::new()
                .num_threads(threads)
                .thread_name(|index| format!("deepfold-prover-{index}"))
                .build()
                .map_err(|_| Error::InvalidParameters("failed to build prover worker pool"))?,
        );
        let sequential_pool = if threads == 1 {
            Arc::clone(&pool)
        } else {
            Arc::new(
                ThreadPoolBuilder::new()
                    .num_threads(1)
                    .thread_name(|_| "deepfold-prover-sequential".to_owned())
                    .build()
                    .map_err(|_| {
                        Error::InvalidParameters("failed to build sequential prover pool")
                    })?,
            )
        };
        Ok(Self {
            threads,
            pool,
            sequential_pool,
        })
    }

    pub fn threads(&self) -> usize {
        self.threads
    }

    pub(crate) fn install<T: Send>(&self, operation: impl FnOnce() -> T + Send) -> T {
        self.pool.install(operation)
    }

    pub(crate) fn install_sequential<T: Send>(&self, operation: impl FnOnce() -> T + Send) -> T {
        self.sequential_pool.install(operation)
    }
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self::new(1).expect("one-worker prover pool is valid")
    }
}
