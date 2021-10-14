with import <nixpkgs> {};

let
  unstable = import <nixos-unstable> {};
in
let
  symfpu = stdenv.mkDerivation rec {
    pname = "symfpu";
    version = "8fbe139bf0071cbe0758d2f6690a546c69ff0053";
    
    src = fetchFromGitHub {
      owner  = "martin-cs";
      repo   = "symfpu";
      rev    = version;
      sha256 = "1jf5lkn67q136ppfacw3lsry369v7mdr1rhidzjpbz18jfy9zl9q";
    };

    installPhase = ''
      mkdir -p $out
      mkdir -p $out/symfpu
      cp -r * $out/symfpu/
    '';
  };

  cadicalCpp = unstable.cadical.overrideAttrs(super: {
    installPhase = super.installPhase + ''
      install -Dm0644 src/cadical.hpp "$dev/include/cadical.hpp"
    '';
  });
in
let
  pythonPackages = python38Packages;
  cvc5 = stdenv.mkDerivation rec {
    pname = "cvc5";
    version = "cvc5-0.0.2";

    src = fetchFromGitHub {
      owner  = "cvc5";
      repo   = "cvc5";
      rev    = version;
      sha256 = "0wzl1lp6kr7f0yz1i7xpmwp6sx3v0qf61p74hfwgcyy7phkv9hsa";
    };

    nativeBuildInputs = [ pkg-config cmake ];
    buildInputs = [ gmp git python3.pkgs.toml gtest libantlr3c antlr3_4 boost jdk python3 ];

    preConfigure = ''
      patchShebangs ./src/
    '';

    cmakeFlags = [
      "-DCMAKE_BUILD_TYPE=Production"
      "-DCaDiCaL_INCLUDE_DIR=${cadicalCpp.dev}/include/"
      "-DCaDiCaL_LIBRARIES=${cadicalCpp.lib}/lib/libcadical.a"
      "-DCaDiCaL_FOUND=1"
      "-DANTLR3_JAR=${antlr3_4}/lib/antlr/antlr-3.4-complete.jar"
      "-DSymFPU_INCLUDE_DIR=${(symfpu)}"
    ];
  };
in
mkShell {
  venvDir = "./.venv";
  buildInputs = [
    pythonPackages.python
    pythonPackages.llvmlite
    pythonPackages.pyparsing
    pythonPackages.venvShellHook
    (cvc5)
    llvm_10
    clang_10
  ];

  postShellHook = ''
    pip install --upgrade pip
  '';

  hardeningDisable = [ "fortify" ];
}
