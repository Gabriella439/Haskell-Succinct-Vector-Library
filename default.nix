{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, criterion, deepseq, doctest, primitive
      , QuickCheck, stdenv, vector
      }:
      mkDerivation {
        pname = "succinct-vector";
        version = "1.0.0";
        src = ./.;
        libraryHaskellDepends = [
          base deepseq primitive QuickCheck vector
        ];
        testHaskellDepends = [ base doctest QuickCheck vector ];
        benchmarkHaskellDepends = [ base criterion vector ];
        description = "Succinct vectors";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = pkgs.haskell.lib.overrideCabal (variant (haskellPackages.callPackage f {})) (drv: {
    preCheck = ''
      export GHC_PACKAGE_PATH=$PWD/dist/package.conf.inplace/:$GHC_PACKAGE_PATH
    '';
  });

in

  if pkgs.lib.inNixShell then drv.env else drv
