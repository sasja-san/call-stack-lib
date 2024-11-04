# call-stack-lib
Rust library implementing (most of) the functionality of Dirbaio/cargo-call-stack.


## Preparing your binary

The library `stack-sizes` requires that your ELF contains a section named 
`.stack_sizes`. For `rustc` to generate this the flag `-Zemit-stack-sizes` is 
needed, which is only available with nightly.


### Nigthly requirements

Look in `Cargo.toml` of this project. The version number for `llvm-sys` in
there tells you what version LLVM you need to have.


For the nightly version you pick, make sure that it's version of llvm (seen by
running `rustc --version -v`) matches the version of `llvm-sys` used by this
project.

*Example:*

This is from `Cargo.toml`:
```toml
llvm-sys = "170.0.1"
```

This means that the LLVM version used by `rustc` should be 17.0.

```default
$ rustc --version -v
rustc 1.78.0-nightly (b11fbfbf3 2024-02-03)
binary: rustc
commit-hash: b11fbfbf351b94c7eecf9e6749a4544a6d4717fa
commit-date: 2024-02-03
host: x86_64-unknown-linux-gnu
release: 1.78.0-nightly
LLVM version: 17.0.6
```


### Set a Nightly for your Project

Easiest is to create a file called `rust-toolchain.toml` in the root of 
your project. Here's an example of one which targets an ARM Cortex-M4.

```toml
[toolchain]
channel = "nightly-2022-09-20"
components = [ "rustfmt", "rustc-dev" ]
targets = [ "thumbv7em-none-eabihf" ]
# targets = [ "wasm32-unknown-unknown", "thumbv2-none-eabi" ]
profile = "minimal"
```

On a linux system, you can then install the rust source component 
for your specific nightly with this command:

```
$ rustup component add rust-src --toolchain nightly-2022-09-20-x86_64-unknown-linux-gnu
```

Adjust per your own system properties.

**OR** you could run a command such as this to install a certain toolchain and
have it set as an override for your current directory.
This command is for `fish`:

```
fish$ set ndate "2022-09-04"; rustup override set nightly-$ndate && rustup component add rust-src --toolchain nightly-"$ndate"-x86_64-unknown-linux-gnu
```

When using the override command it will be saved in `~/.rustup/settings.toml`.

### Cargo.toml

Configure your Cargo project to use *fat LTO*. This is not the default 
configuration (as of Rust 1.63) so you'll need to add this to your `Cargo.toml`:

```toml
[profile.release]
lto = 'fat'
```

### .cargo/config.toml

Configure the linker to embed LLVM bitcode inside the final ELF.
Add this to `.cargo/config.toml`:

```toml
[target.'cfg(all(target_arch = "arm", target_os = "none"))']
rustflags = [
  "-Zemit-stack-sizes",
  "-Clinker-plugin-lto",
  "-Clink-arg=-mllvm=-lto-embed-bitcode=optimized",
  "-Clink-arg=-mllvm=-stack-size-section",
]
```

It is recommended to use `build-std` so that libcore compiler flags match your
main binary's. Add this to `.cargo/config.toml`:

```toml
[unstable]
build-std = ["compiler_builtins", "core"]
```

### Building your Binary

Build your project in release mode:

```
$ cargo build --release
```

Then point your implementation of the library towards the binary.


## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.


