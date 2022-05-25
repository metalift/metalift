let
  # updated 3/15/22
  pkgs = import (fetchTarball https://github.com/nixos/nixpkgs/archive/cbd40c72b2603ab54e7208f99f9b35fc158bc009.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/dfd82985c273aac6eced03625f454b334daae2e8.tar.gz) { };
in
with pkgs;

mkShell {
  buildInputs = [
    (python38.withPackages (p: with p; [
      poetry
    ]))

    unstable.cvc5
    cmake
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];
}
