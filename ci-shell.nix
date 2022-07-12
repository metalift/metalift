let
  # updated 7/11/22
  pkgs = import (fetchTarball https://github.com/nixos/nixpkgs/archive/ccf8bdf72624521358be6bb7d9b524c4cbcf7aff.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/b39924fc7764c08ae3b51beef9a3518c414cdb7d.tar.gz) { };
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
