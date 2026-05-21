use thiserror::Error;

#[derive(Debug, Error)]
pub enum FoldingError {
    #[error("PESAT instance/witness shape mismatch: {0}")]
    ShapeMismatch(String),

    #[error("constraint {idx} does not vanish: p_hat[{idx}](x, w) = {value}")]
    ConstraintNonZero { idx: usize, value: String },

    #[error("degree bound exceeded: expected ≤ {expected}, got {actual}")]
    DegreeExceeded { expected: usize, actual: usize },

    #[error("codeword length mismatch: n={n}, got={got}")]
    CodewordLengthMismatch { n: usize, got: usize },
}

pub type Result<T> = std::result::Result<T, FoldingError>;
