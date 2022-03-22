let
  # updated 3/15/22
  pkgs = import (fetchTarball https://github.com/nixos/nixpkgs/archive/0f85665118d850aae5164d385d24783d0b16cf1b.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/b0e141e3fe13ec21f50429773d2e3890e02a80da.tar.gz) { };
in
with pkgs;

let
  cvc5 = callPackage ./cvc5.nix { unstable = unstable; };
in
mkShell {
  venvDir = "./.venv";
  buildInputs = [
    (python38.withPackages (p: with p; [
      pyparsing
    ]))

    cvc5
    cmake
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];

  PYTHONPATH="llvmlite";
}
