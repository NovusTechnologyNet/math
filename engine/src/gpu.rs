//! CUDA back end for the machine-word stage.
//!
//! The NVIDIA driver library (nvcuda.dll) is loaded at run time, so the program
//! still starts, and falls back to the CPU, on a machine without it. The kernel
//! is kernel.cu, compiled ahead of time to PTX and embedded here.

use crate::word::{Consts, Items};
use crate::word2::Consts2;
use std::ffi::{c_void, CStr, CString};
use std::os::raw::c_char;
use std::ptr::null_mut;

const PTX: &str = include_str!("../kernel.ptx");
const BLOCK: u32 = 256;
/// Fixed cost of one item (setup, final inversion) in units of loop iterations.
const OVERHEAD: u64 = 24;
const MAX_PER_LAUNCH: usize = 1 << 23;

#[link(name = "kernel32")]
extern "system" {
    fn LoadLibraryA(name: *const c_char) -> *mut c_void;
    fn GetProcAddress(module: *mut c_void, name: *const c_char) -> *mut c_void;
}

type P = *mut c_void;
type Launch = unsafe extern "system" fn(P, u32, u32, u32, u32, u32, u32, u32, P, *mut P, *mut P) -> i32;

pub struct Gpu {
    pub name: String,
    /// Loop iterations allowed in one kernel launch (keeps launches short).
    pub budget: u64,
    f_large: P,
    f_small: P,
    f_large2: P,
    f_small2: P,
    mem_alloc: unsafe extern "system" fn(*mut u64, usize) -> i32,
    mem_free: unsafe extern "system" fn(u64) -> i32,
    h2d: unsafe extern "system" fn(u64, *const c_void, usize) -> i32,
    d2h: unsafe extern "system" fn(*mut c_void, u64, usize) -> i32,
    launch: Launch,
    sync: unsafe extern "system" fn() -> i32,
}

unsafe fn sym<T: Copy>(lib: P, name: &str) -> Result<T, String> {
    let c = CString::new(name).unwrap();
    let p = GetProcAddress(lib, c.as_ptr());
    if p.is_null() {
        return Err(format!("the CUDA driver has no function {}", name));
    }
    Ok(std::mem::transmute_copy::<P, T>(&p))
}

fn ck(code: i32, what: &str) -> Result<(), String> {
    if code == 0 {
        Ok(())
    } else {
        Err(format!("CUDA error {} in {}", code, what))
    }
}

impl Gpu {
    /// Must be called on the thread that will use the Gpu (the context is per thread).
    pub fn new() -> Result<Gpu, String> {
        unsafe {
            let lib = LoadLibraryA(b"nvcuda.dll\0".as_ptr() as *const c_char);
            if lib.is_null() {
                return Err("nvcuda.dll not found (no NVIDIA driver)".into());
            }
            let init: unsafe extern "system" fn(u32) -> i32 = sym(lib, "cuInit")?;
            let dev_get: unsafe extern "system" fn(*mut i32, i32) -> i32 = sym(lib, "cuDeviceGet")?;
            let dev_name: unsafe extern "system" fn(*mut c_char, i32, i32) -> i32 =
                sym(lib, "cuDeviceGetName")?;
            let ctx_create: unsafe extern "system" fn(*mut P, u32, i32) -> i32 =
                sym(lib, "cuCtxCreate_v2")?;
            let mod_load: unsafe extern "system" fn(*mut P, *const c_void) -> i32 =
                sym(lib, "cuModuleLoadData")?;
            let mod_fn: unsafe extern "system" fn(*mut P, P, *const c_char) -> i32 =
                sym(lib, "cuModuleGetFunction")?;

            ck(init(0), "cuInit")?;
            let mut dev = 0i32;
            ck(dev_get(&mut dev, 0), "cuDeviceGet")?;
            let mut buf = [0 as c_char; 128];
            ck(dev_name(buf.as_mut_ptr(), 128, dev), "cuDeviceGetName")?;
            let name = CStr::from_ptr(buf.as_ptr()).to_string_lossy().into_owned();
            let mut ctx: P = null_mut();
            ck(ctx_create(&mut ctx, 0, dev), "cuCtxCreate")?;
            let image = CString::new(PTX).map_err(|_| "bad PTX".to_string())?;
            let mut module: P = null_mut();
            ck(mod_load(&mut module, image.as_ptr() as *const c_void), "cuModuleLoadData")?;
            let mut f_large: P = null_mut();
            let mut f_small: P = null_mut();
            let n1 = CString::new("large_primes").unwrap();
            let n2 = CString::new("small_items").unwrap();
            ck(mod_fn(&mut f_large, module, n1.as_ptr()), "cuModuleGetFunction")?;
            ck(mod_fn(&mut f_small, module, n2.as_ptr()), "cuModuleGetFunction")?;
            let mut f_large2: P = null_mut();
            let mut f_small2: P = null_mut();
            let n3 = CString::new("large_primes2").unwrap();
            let n4 = CString::new("small_items2").unwrap();
            ck(mod_fn(&mut f_large2, module, n3.as_ptr()), "cuModuleGetFunction")?;
            ck(mod_fn(&mut f_small2, module, n4.as_ptr()), "cuModuleGetFunction")?;
            Ok(Gpu {
                name,
                budget: 1 << 26,
                f_large,
                f_small,
                f_large2,
                f_small2,
                mem_alloc: sym(lib, "cuMemAlloc_v2")?,
                mem_free: sym(lib, "cuMemFree_v2")?,
                h2d: sym(lib, "cuMemcpyHtoD_v2")?,
                d2h: sym(lib, "cuMemcpyDtoH_v2")?,
                launch: sym(lib, "cuLaunchKernel")?,
                sync: sym(lib, "cuCtxSynchronize")?,
            })
        }
    }

    unsafe fn up<T>(&self, data: &[T]) -> u64 {
        let bytes = std::mem::size_of_val(data);
        let mut d = 0u64;
        ck((self.mem_alloc)(&mut d, bytes.max(8)), "cuMemAlloc").unwrap();
        ck((self.h2d)(d, data.as_ptr() as *const c_void, bytes), "cuMemcpyHtoD").unwrap();
        d
    }

    unsafe fn run(&self, f: P, n: u32, params: &mut [P]) {
        let grid = (n + BLOCK - 1) / BLOCK;
        ck(
            (self.launch)(f, grid, 1, 1, BLOCK, 1, 1, 0, null_mut(), params.as_mut_ptr(), null_mut()),
            "cuLaunchKernel",
        )
        .unwrap();
        ck((self.sync)(), "kernel run").unwrap();
    }

    /// C_p for primes above sqrt(la); the list must be in ascending order.
    pub fn large(&self, primes: &[u64], k: &Consts) -> Vec<u64> {
        let n = primes.len();
        let mut out = vec![0u64; n];
        if n == 0 {
            return out;
        }
        unsafe {
            let d_p = self.up(primes);
            let mut d_out = 0u64;
            ck((self.mem_alloc)(&mut d_out, n * 8), "cuMemAlloc").unwrap();
            let (mut m, mut la, mut lb, mut lc, mut ld) = (k.m, k.la, k.lb, k.lc, k.ld);
            let mut start = 0usize;
            while start < n {
                // runs get shorter as primes grow, so the first prime bounds the cost
                let per = (k.la / primes[start] + 1) / 2 + OVERHEAD;
                let cnt = ((self.budget / per).max(1) as usize).min(MAX_PER_LAUNCH).min(n - start);
                let mut a = d_p + (start * 8) as u64;
                let mut b = d_out + (start * 8) as u64;
                let mut c = cnt as u32;
                let mut params: [P; 8] = [
                    &mut a as *mut _ as P,
                    &mut b as *mut _ as P,
                    &mut c as *mut _ as P,
                    &mut m as *mut _ as P,
                    &mut la as *mut _ as P,
                    &mut lb as *mut _ as P,
                    &mut lc as *mut _ as P,
                    &mut ld as *mut _ as P,
                ];
                self.run(self.f_large, c, &mut params);
                start += cnt;
            }
            ck((self.d2h)(out.as_mut_ptr() as *mut c_void, d_out, n * 8), "cuMemcpyDtoH").unwrap();
            (self.mem_free)(d_p);
            (self.mem_free)(d_out);
        }
        out
    }

    /// The cheaper formula: C_p for primes above sqrt(l3), in ascending order.
    pub fn large2(&self, primes: &[u64], k: &Consts2) -> Vec<u64> {
        let n = primes.len();
        let mut out = vec![0u64; n];
        if n == 0 {
            return out;
        }
        unsafe {
            let d_p = self.up(primes);
            let mut d_out = 0u64;
            ck((self.mem_alloc)(&mut d_out, n * 8), "cuMemAlloc").unwrap();
            let (mut m, mut k0, mut l3) = (k.m, k.k0, k.l3);
            let mut start = 0usize;
            while start < n {
                let per = (k.l3 / primes[start] + 1) / 2 + OVERHEAD;
                let cnt = ((self.budget / per).max(1) as usize).min(MAX_PER_LAUNCH).min(n - start);
                let mut a = d_p + (start * 8) as u64;
                let mut b = d_out + (start * 8) as u64;
                let mut c = cnt as u32;
                let mut params: [P; 6] = [
                    &mut a as *mut _ as P,
                    &mut b as *mut _ as P,
                    &mut c as *mut _ as P,
                    &mut m as *mut _ as P,
                    &mut k0 as *mut _ as P,
                    &mut l3 as *mut _ as P,
                ];
                self.run(self.f_large2, c, &mut params);
                start += cnt;
            }
            ck((self.d2h)(out.as_mut_ptr() as *mut c_void, d_out, n * 8), "cuMemcpyDtoH").unwrap();
            (self.mem_free)(d_p);
            (self.mem_free)(d_out);
        }
        out
    }

    /// The cheaper formula: one result per explicit work item.
    pub fn small2(&self, it: &Items, k: &Consts2) -> Vec<u64> {
        let n = it.p.len();
        let mut out = vec![0u64; n];
        if n == 0 {
            return out;
        }
        unsafe {
            let d = [self.up(&it.p), self.up(&it.q), self.up(&it.phi), self.up(&it.j0)];
            let d_len = self.up(&it.len);
            let mut d_out = 0u64;
            ck((self.mem_alloc)(&mut d_out, n * 8), "cuMemAlloc").unwrap();
            let (mut m, mut k0) = (k.m, k.k0);
            let mut start = 0usize;
            while start < n {
                let mut end = start;
                let mut work = 0u64;
                while end < n && end - start < MAX_PER_LAUNCH && (work < self.budget || end == start) {
                    work += it.len[end] as u64 + OVERHEAD;
                    end += 1;
                }
                let off = (start * 8) as u64;
                let (mut a0, mut a1, mut a2, mut a3) = (d[0] + off, d[1] + off, d[2] + off, d[3] + off);
                let mut a4 = d_len + (start * 4) as u64;
                let mut b = d_out + off;
                let mut c = (end - start) as u32;
                let mut params: [P; 9] = [
                    &mut a0 as *mut _ as P,
                    &mut a1 as *mut _ as P,
                    &mut a2 as *mut _ as P,
                    &mut a3 as *mut _ as P,
                    &mut a4 as *mut _ as P,
                    &mut b as *mut _ as P,
                    &mut c as *mut _ as P,
                    &mut m as *mut _ as P,
                    &mut k0 as *mut _ as P,
                ];
                self.run(self.f_small2, c, &mut params);
                start = end;
            }
            ck((self.d2h)(out.as_mut_ptr() as *mut c_void, d_out, n * 8), "cuMemcpyDtoH").unwrap();
            for x in d {
                (self.mem_free)(x);
            }
            (self.mem_free)(d_len);
            (self.mem_free)(d_out);
        }
        out
    }

    /// One result per explicit work item.
    pub fn small(&self, it: &Items, k: &Consts) -> Vec<u64> {
        let n = it.p.len();
        let mut out = vec![0u64; n];
        if n == 0 {
            return out;
        }
        unsafe {
            let d = [self.up(&it.p), self.up(&it.q), self.up(&it.phi), self.up(&it.j0)];
            let d_len = self.up(&it.len);
            let mut d_out = 0u64;
            ck((self.mem_alloc)(&mut d_out, n * 8), "cuMemAlloc").unwrap();
            let (mut m, mut la, mut lb, mut lc, mut ld) = (k.m, k.la, k.lb, k.lc, k.ld);
            let mut start = 0usize;
            while start < n {
                let mut end = start;
                let mut work = 0u64;
                while end < n && end - start < MAX_PER_LAUNCH && (work < self.budget || end == start) {
                    work += it.len[end] as u64 + OVERHEAD;
                    end += 1;
                }
                let off = (start * 8) as u64;
                let (mut a0, mut a1, mut a2, mut a3) = (d[0] + off, d[1] + off, d[2] + off, d[3] + off);
                let mut a4 = d_len + (start * 4) as u64;
                let mut b = d_out + off;
                let mut c = (end - start) as u32;
                let mut params: [P; 12] = [
                    &mut a0 as *mut _ as P,
                    &mut a1 as *mut _ as P,
                    &mut a2 as *mut _ as P,
                    &mut a3 as *mut _ as P,
                    &mut a4 as *mut _ as P,
                    &mut b as *mut _ as P,
                    &mut c as *mut _ as P,
                    &mut m as *mut _ as P,
                    &mut la as *mut _ as P,
                    &mut lb as *mut _ as P,
                    &mut lc as *mut _ as P,
                    &mut ld as *mut _ as P,
                ];
                self.run(self.f_small, c, &mut params);
                start = end;
            }
            ck((self.d2h)(out.as_mut_ptr() as *mut c_void, d_out, n * 8), "cuMemcpyDtoH").unwrap();
            for x in d {
                (self.mem_free)(x);
            }
            (self.mem_free)(d_len);
            (self.mem_free)(d_out);
        }
        out
    }
}
