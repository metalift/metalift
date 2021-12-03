{ pkgs, unstable }:
with pkgs;

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
in
stdenv.mkDerivation rec {
  pname = "cvc5";
  version = "cvc5-0.0.4";

  src = fetchFromGitHub {
    owner  = "cvc5";
    repo   = "cvc5";
    rev    = version;
    sha256 = "0i4qh9qavhmfz9xd2ifb5yk38p6v1qvgikqwb5jz55ns4459iff0";
  };

  nativeBuildInputs = [ pkg-config cmake ];
  buildInputs = [ unstable.cadical.dev symfpu gmp git python3.pkgs.toml gtest libantlr3c antlr3_4 boost jdk python3 ];

  preConfigure = ''
    patchShebangs ./src/
  '';

  cmakeFlags = [
    "-DCMAKE_BUILD_TYPE=Production"
    "-DBUILD_SHARED_LIBS=1"
    "-DANTLR3_JAR=${antlr3_4}/lib/antlr/antlr-3.4-complete.jar"
  ];
}
