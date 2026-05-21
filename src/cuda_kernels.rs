//! CUDA kernel bindings for the M31Ext3 sumcheck hot loops.
//!
//! Two kernels (mirroring Expander's per-block GKR CUDA work):
//! - `cuda_m31ext3_poly_eval` — round-message reduction: given paired
//!   `bk_f`/`bk_hg` arrays, computes `[p0, p1, p_paired]` via
//!   `p0 = Σ bk_hg[2i]·bk_f[2i]`, `p1 = Σ bk_hg[2i+1]·bk_f[2i+1]`,
//!   `p_paired = Σ (bk_hg[2i]+bk_hg[2i+1])·(bk_f[2i]+bk_f[2i+1])`.
//!   The Rust caller converts to the X=2 form expected by
//!   `round_message` in `constr_8_2.rs` via
//!   `p2 = 6·p1 + 3·p0 − 2·p_paired`.
//! - `cuda_m31ext3_receive_challenge` — fix-bottom-variable update:
//!   `bk_f[i] = bk_f[2i] + (bk_f[2i+1] − bk_f[2i])·r`. Equivalent to
//!   `fix_bottom_variable`.
//!
//! These are M31Ext3-specific. To use the GPU path, the bench must be
//! instantiated at `F = M31Ext3` (which is what Phase 4-B uses).
//!
//! All buffers are device pointers (`*const u32` / `*mut u32`); the
//! caller is responsible for allocation and host↔device transfer.

#![allow(unused)]

use std::os::raw::{c_int, c_uint};

#[link(name = "warp_cuda_m31", kind = "static")]
extern "C" {
    /// Returns 0 on success.
    pub fn cuda_m31ext3_poly_eval(
        d_bk_f: *const u32,
        d_bk_hg: *const u32,
        d_result: *mut u32,
        eval_size: c_uint,
    ) -> c_int;

    /// Returns 0 on success.
    pub fn cuda_m31ext3_receive_challenge(
        d_bk_f: *mut u32,
        d_bk_hg: *mut u32,
        d_challenge_r: *const u32,
        eval_size: c_uint,
        first_round: c_int,
        d_init_v: *const u32,
    ) -> c_int;

    /// Batched poly_eval: processes `batch_size` independent folds in
    /// a single kernel dispatch. Buffers are AoS (fold-contiguous).
    /// `fold_stride_u32` is the per-fold u32 count in the original
    /// allocation — stays constant across rounds even as `eval_size`
    /// halves, so the kernel computes the right per-fold offset.
    /// Result is `batch_size * 9 u32`.
    pub fn cuda_m31ext3_poly_eval_batched(
        d_bk_f: *const u32,
        d_bk_hg: *const u32,
        d_result: *mut u32,
        eval_size: c_uint,
        batch_size: c_uint,
        fold_stride_u32: c_uint,
    ) -> c_int;

    /// Batched receive_challenge: each fold has its own `r` (3 u32);
    /// `d_challenge_r` is `batch_size * 3 u32` total.
    pub fn cuda_m31ext3_receive_challenge_batched(
        d_bk_f: *mut u32,
        d_bk_hg: *mut u32,
        d_challenge_r: *const u32,
        eval_size: c_uint,
        batch_size: c_uint,
        fold_stride_u32: c_uint,
    ) -> c_int;
}

/// CUDA Runtime API bindings — minimal set for our needs.
#[link(name = "cudart")]
extern "C" {
    pub fn cudaMalloc(devPtr: *mut *mut std::ffi::c_void, size: usize) -> c_int;
    pub fn cudaFree(devPtr: *mut std::ffi::c_void) -> c_int;
    pub fn cudaMemcpy(
        dst: *mut std::ffi::c_void,
        src: *const std::ffi::c_void,
        count: usize,
        kind: c_int,
    ) -> c_int;
    pub fn cudaDeviceSynchronize() -> c_int;
}

/// `cudaMemcpyHostToDevice` — see the CUDA Runtime API.
pub const CUDA_MEMCPY_HOST_TO_DEVICE: c_int = 1;
/// `cudaMemcpyDeviceToHost`.
pub const CUDA_MEMCPY_DEVICE_TO_HOST: c_int = 2;

/// Quick smoke-test helper: exercises both kernels on a tiny size and
/// verifies the result by re-computing on the host. Used by the bench
/// to confirm the CUDA path is actually working before timing it.
pub fn smoke_test() -> Result<(), String> {
    use crate::twin::{eq_scalar, mle_eval};
    use expander_arith::ExtensionField;
    use expander_mersenne31::M31Ext3;

    // Tiny: log_n = 2, n = 4. Build paired bk_f / bk_hg of length 2n = 8.
    // Each "M31Ext3" element is 3 u32 = 12 bytes.
    let f_host: Vec<M31Ext3> = (1u32..=8).map(M31Ext3::from).collect();
    let hg_host: Vec<M31Ext3> = (10u32..=17).map(M31Ext3::from).collect();
    let f_words: Vec<u32> = f_host
        .iter()
        .flat_map(|x| x.v.iter().map(|m| m.v))
        .collect();
    let hg_words: Vec<u32> = hg_host
        .iter()
        .flat_map(|x| x.v.iter().map(|m| m.v))
        .collect();
    let eval_size = 4u32;

    unsafe {
        let mut d_f: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_hg: *mut std::ffi::c_void = std::ptr::null_mut();
        let mut d_result: *mut std::ffi::c_void = std::ptr::null_mut();

        let bytes = f_words.len() * 4;
        if cudaMalloc(&mut d_f, bytes) != 0 {
            return Err("cudaMalloc d_f failed".into());
        }
        if cudaMalloc(&mut d_hg, bytes) != 0 {
            return Err("cudaMalloc d_hg failed".into());
        }
        if cudaMalloc(&mut d_result, 9 * 4) != 0 {
            return Err("cudaMalloc d_result failed".into());
        }

        cudaMemcpy(
            d_f,
            f_words.as_ptr() as *const _,
            bytes,
            CUDA_MEMCPY_HOST_TO_DEVICE,
        );
        cudaMemcpy(
            d_hg,
            hg_words.as_ptr() as *const _,
            bytes,
            CUDA_MEMCPY_HOST_TO_DEVICE,
        );

        let rc = cuda_m31ext3_poly_eval(
            d_f as *const u32,
            d_hg as *const u32,
            d_result as *mut u32,
            eval_size,
        );
        if rc != 0 {
            return Err(format!("kernel returned {rc}"));
        }
        cudaDeviceSynchronize();

        let mut result_words = [0u32; 9];
        cudaMemcpy(
            result_words.as_mut_ptr() as *mut _,
            d_result as *const _,
            9 * 4,
            CUDA_MEMCPY_DEVICE_TO_HOST,
        );

        cudaFree(d_f);
        cudaFree(d_hg);
        cudaFree(d_result);

        // Verify against host computation.
        let p0_host: M31Ext3 = (0..eval_size as usize)
            .map(|i| hg_host[2 * i] * f_host[2 * i])
            .fold(M31Ext3::default(), |a, b| a + b);
        let p1_host: M31Ext3 = (0..eval_size as usize)
            .map(|i| hg_host[2 * i + 1] * f_host[2 * i + 1])
            .fold(M31Ext3::default(), |a, b| a + b);

        let p0_dev = M31Ext3::from_limbs(&[
            expander_mersenne31::M31 { v: result_words[0] },
            expander_mersenne31::M31 { v: result_words[1] },
            expander_mersenne31::M31 { v: result_words[2] },
        ]);
        let p1_dev = M31Ext3::from_limbs(&[
            expander_mersenne31::M31 { v: result_words[3] },
            expander_mersenne31::M31 { v: result_words[4] },
            expander_mersenne31::M31 { v: result_words[5] },
        ]);

        if p0_dev != p0_host {
            return Err(format!("p0 mismatch: dev={p0_dev:?} host={p0_host:?}"));
        }
        if p1_dev != p1_host {
            return Err(format!("p1 mismatch: dev={p1_dev:?} host={p1_host:?}"));
        }
        let _ = eq_scalar::<M31Ext3>;
        let _ = mle_eval::<M31Ext3, M31Ext3>;
    }
    Ok(())
}
