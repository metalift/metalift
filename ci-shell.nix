let
  # updated 3/15/22
  pkgs = import (fetchTarball https://github.com/nixos/nixpkgs/archive/cbd40c72b2603ab54e7208f99f9b35fc158bc009.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/dfd82985c273aac6eced03625f454b334daae2e8.tar.gz) { };
  poetry2nixLatest = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/2a2193eb0677a8801c3b414f67bacf499bd0b6fc.tar.gz) { };
in
with pkgs;

(poetry2nixLatest.poetry2nix.mkPoetryEnv {
  python = python38;
  projectDir = ./.;
  preferWheels = true;
}).env.overrideAttrs(old: {
  buildInputs = [
    unstable.cvc5
    cmake
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];
})
