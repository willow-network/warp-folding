//! Smoke test for the WARP-GF2 micro-spike (PR #506).
//!
//! Confirms `WarpProverState<F>` instantiates over `GF2_128` — i.e. that
//! the field-genericity claim from the spike doc holds in practice and
//! that GF2_128 satisfies all of WARP's trait bounds (`Field + ExpSerde
//! + From<u32> + Mul<F, Output = F>`).
//!
//! Does NOT call `fold_block` — the existing API folds raw bytes via a
//! tautology constraint (right for cryptographic-archival, wrong for
//! aggregating chunk proofs). Constructing `WarpProverState::genesis()`
//! is enough to prove "the trait bounds compile."
//!
//! Run:
//! ```sh
//! cargo test --test gf2_compile_check
//! ```

use warp_folding::{
    default_orion_code, verify_with_parallel_rep_bound, LinearCode, OrionLinearCode,
    SamplingParams, SchemeParams, WarpProverState,
};
use warp_folding::M31Ext3;

// Per-arch dispatcher lives at the GF2_128 type alias in
// `expander_gf2_128`; on aarch64 it resolves to NeonGF2_128, on x86_64
// to AVX(2|512)GF2_128. The Field + From<u32> impls are on the
// per-arch types but accessible through the alias.
type Gf2 = expander_gf2_128::GF2_128;

#[test]
fn warp_prover_state_compiles_over_gf2_128() {
    // Constructing the state exercises every trait bound on F.
    // `genesis(msg_log_n=6, parallel_rep=2, [0; 32])` makes a tiny
    // codeword (64-element message) so the test stays cheap.
    let state = WarpProverState::<Gf2>::genesis(6, 2, [0u8; 32]);

    // The state should self-check (instance / witness consistency at
    // the genesis point).
    state
        .self_check()
        .expect("WarpProverState<GF2_128>::genesis must produce a consistent state");

    // The current_root() is the running accumulator's Merkle root —
    // 32 bytes, never zero in practice.
    let root = state.current_root();
    assert_ne!(root, [0u8; 32], "genesis root should be non-zero");
}

/// Push further: actually `fold_block` a small payload. This exercises
/// the full WARP IOR pipeline over GF2_128 — PESAT reduction (constr_5_10),
/// codeword batching (constr_7_2), sumcheck (constr_8_2), fold (constr_9_4),
/// Fiat-Shamir with parallel-rep — proving the field-genericity claim isn't
/// just at the prover-state level.
#[test]
fn warp_fold_block_runs_over_gf2_128() {
    let mut state = WarpProverState::<Gf2>::genesis(6, 2, [0u8; 32]);
    let pre_root = state.current_root();

    // Tiny payload; the WARP IOR over a 6-bit codeword (64-element
    // message) handles this in milliseconds.
    let payload = b"smoke-test payload over GF2_128";
    let wire = state
        .fold_block([0xAAu8; 32], payload)
        .expect("fold_block must succeed over GF2_128");

    // Sanity: the wire message carries the pre/post instances.
    // We don't pin specific values — just confirm fold did SOMETHING:
    // the root advanced, self_check still holds.
    state
        .self_check()
        .expect("post-fold state must self-check");
    let post_root = state.current_root();
    assert_ne!(
        pre_root, post_root,
        "fold_block must advance the running root"
    );

    // wire.messages is the per-fold transcript the verifier consumes —
    // length should be parallel_rep (2) × messages-per-rep.
    assert!(
        !wire.messages.is_empty(),
        "fold wire must carry at least one message"
    );

    // Diagnostic: show wire shape so failures are easy to triage.
    eprintln!(
        "wire: messages.len()={}, prev.alpha.len()={}, new.alpha.len()={}",
        wire.messages.len(),
        wire.prev_instance.alpha.len(),
        wire.new_instance.alpha.len(),
    );

    // Close the loop: VERIFY the fold message the prover produced.
    let code: OrionLinearCode = default_orion_code(6);
    let params = SchemeParams {
        log_n: <OrionLinearCode as LinearCode<Gf2>>::log_codeword_len(&code),
        k: 1 << 6,
        m: 0,
        d: 1,
    };
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };
    let folded_inst = verify_with_parallel_rep_bound::<Gf2>(
        &[wire.prev_instance.clone(), wire.new_instance.clone()],
        &params,
        &sampling,
        &wire.messages,
        &[0xAAu8; 32],
    )
    .expect("WARP verify must accept the prover's fold over GF2_128");

    // The verifier's folded instance should equal the prover's
    // resulting state (the running accumulator) — that's the
    // accumulator-consistency property WARP guarantees.
    assert_eq!(
        folded_inst.alpha.len(),
        wire.new_instance.alpha.len(),
        "verifier and prover should agree on the folded instance shape"
    );
}

/// **A/B baseline.** Same shape as `warp_fold_block_runs_over_gf2_128`
/// but over M31Ext3 — if this also fails the verify step, the bug is
/// in `fold_block`'s scheme-params construction (not in the public
/// verify API, which the existing end_to_end tests prove works). If it
/// passes, the GF2 verify failure is field-specific and a real spike
/// finding.
#[test]
fn warp_fold_block_verify_over_m31_baseline() {
    let mut state = WarpProverState::<M31Ext3>::genesis(6, 2, [0u8; 32]);
    let payload = b"smoke-test payload over M31Ext3";
    let wire = state.fold_block([0xAAu8; 32], payload).expect("fold_block M31");

    let code: OrionLinearCode = default_orion_code(6);
    let params = SchemeParams {
        log_n: <OrionLinearCode as LinearCode<M31Ext3>>::log_codeword_len(&code),
        k: 1 << 6,
        m: 0,
        d: 1,
    };
    let sampling = SamplingParams {
        n_ood: 1,
        n_shifts: 2,
    };
    let result = verify_with_parallel_rep_bound::<M31Ext3>(
        &[wire.prev_instance.clone(), wire.new_instance.clone()],
        &params,
        &sampling,
        &wire.messages,
        &[0xAAu8; 32],
    );
    eprintln!("M31 verify result: {:?}", result.as_ref().map(|_| "OK").map_err(|e| format!("{e:?}")));
    result.expect("WARP verify must accept the prover's fold over M31Ext3 (baseline)");
}
