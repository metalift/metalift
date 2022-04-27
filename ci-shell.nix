let
  # updated 3/15/22
  pkgs = import (fetchTarball https://github.com/nixos/nixpkgs/archive/3a9e0f239d80fa134e8fcbdee4dfc793902da37e.tar.gz) { };
  unstable = import (fetchTarball https://github.com/NixOS/nixpkgs/archive/6a323903ad07de6680169bb0423c5cea9db41d82.tar.gz) { };
in
with pkgs;

mkShell {
  buildInputs = [
    (python38.withPackages (p: with p; [
      pyparsing
    ]))

    unstable.cvc5
    cmake
    llvm_11
    clang_11
  ];

  hardeningDisable = [ "fortify" ];

  PYTHONPATH="llvmlite";
}
