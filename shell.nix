let
  pkgs = import <nixpkgs> {};
  poetry2nixLatest = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/2a2193eb0677a8801c3b414f67bacf499bd0b6fc.tar.gz) { };
in
with pkgs;

(poetry2nixLatest.poetry2nix.mkPoetryEnv {
  python = python38;
  projectDir = ./.;
  preferWheels = true;
}).env.overrideAttrs(old: {
  buildInputs = [
    cvc5
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];

  NIX_LD_LIBRARY_PATH = lib.makeLibraryPath [
    stdenv.cc.cc
  ];

  NIX_LD = lib.fileContents "${stdenv.cc}/nix-support/dynamic-linker";
})
