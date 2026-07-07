// Build script for warp-folding.
//
// When the `cuda` feature is enabled, compiles the M31Ext3 sumcheck
// CUDA kernels via nvcc. Kernels live under `cuda/` and are copied
// verbatim from Expander's `sumcheck/cuda_m31/` to keep the build
// self-contained. Mirror of Expander's own build pattern.

fn main() {
    #[cfg(feature = "cuda")]
    {
        use std::env;

        let nvcc = match env::var("NVCC") {
            Ok(var) => which::which(var),
            Err(_) => which::which("nvcc"),
        };

        if let Ok(_nvcc_path) = nvcc {
            let mut build = cc::Build::new();
            build.cuda(true);
            // Target Ampere (sm_80) with backward compat to Volta (sm_70).
            // Picks up consumer cards (RTX 30/40/50 series) and data
            // center cards (A100, H100, L40S, etc.).
            build.flag("-arch=sm_80");
            build.flag("-gencode").flag("arch=compute_70,code=sm_70");
            build.flag("-t0");

            #[cfg(not(target_env = "msvc"))]
            {
                build.flag("-Xcompiler").flag("-Wno-unused-function");
            }

            build.include("cuda");
            build
                .file("cuda/m31_sumcheck.cu")
                .file("cuda/m31_sumcheck_batched.cu")
                .compile("warp_cuda_m31");

            // Link against CUDA runtime for cudaMalloc / cudaMemcpy.
            println!("cargo:rustc-link-lib=cudart");
            println!("cargo:rerun-if-changed=cuda");
        } else {
            println!(
                "cargo:warning=nvcc not found; building warp-folding's `cuda` feature \
                 with kernels disabled. Build will succeed but `cuda_kernels_built` cfg \
                 will not be set, so the GPU path is unreachable."
            );
        }
    }
}
