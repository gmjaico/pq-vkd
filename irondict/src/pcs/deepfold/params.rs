/// Parameters for the Intiliasation for the Deepfold PCS
use crate::Result;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Parameters {
    pub num_vars: usize,
    pub log_blowup: usize,
    pub num_queries: usize,
    pub security_bits: usize,
}

impl Parameters {
    pub const DEFAULT_LOG_BLOWUP: usize = 3;
    pub const DEFAULT_SECURITY_BITS: usize = 100;
    pub const DEFAULT_NUM_QUERIES: usize = 34;
    pub const MAX_NUM_VARS: usize = 24;

    pub fn new(num_vars: usize) -> Result<Self> {
        if num_vars > Self::MAX_NUM_VARS {
            return Err(crate::Error::InvalidParameters(
                "polynomial dimension exceeds the supported maximum",
            ));
        }
        let params = Self {
            num_vars,
            log_blowup: Self::DEFAULT_LOG_BLOWUP,
            num_queries: Self::DEFAULT_NUM_QUERIES,
            security_bits: Self::DEFAULT_SECURITY_BITS,
        };

        Ok(params)
    }

    pub fn validate(&self) -> Result<()> {
        if self.num_vars > Self::MAX_NUM_VARS {
            return Err(crate::Error::InvalidParameters(
                "polynomial dimension exceeds the supported maximum",
            ));
        }
        if self.log_blowup != Self::DEFAULT_LOG_BLOWUP
            || self.num_queries != Self::DEFAULT_NUM_QUERIES
            || self.security_bits != Self::DEFAULT_SECURITY_BITS
        {
            return Err(crate::Error::InvalidParameters(
                "unsupported DeepFold parameter configuration",
            ));
        }
        Ok(())
    }

    pub fn polynomial_size(&self) -> usize {
        1usize << self.num_vars
    }

    pub fn domain_size(&self) -> usize {
        1usize << (self.num_vars + self.log_blowup)
    }
}
