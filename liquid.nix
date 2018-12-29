let

  pkgs = import <nixpkgs> { };

  liquid-fixpoint-src = pkgs.fetchFromGitHub {
    owner = "ucsd-progsys";
    repo = "liquid-fixpoint";
    rev = "f3a7f69ba727f18261a6e1a5bd5d0a0098380d91";
    sha256 = "0j35a9692csm84zb5mizj24d4lr86fxznrjg8nww2ms5nr2g67dz";
  };

  liquidhaskell-src = pkgs.fetchFromGitHub {
    owner = "ucsd-progsys";
    repo = "liquidhaskell";
    rev = "57213512a9d69093c12d644b21dbf9da95811894";
    sha256 = "1dlpj2v89l8iqqiyzdf69m3m5ifwlac15bn7dkpz2hr2gzqg7aq1";
  };

  haskellPackages = pkgs.haskell.packages.ghc844.extend (self: super: {
    liquid-fixpoint = self.callCabal2nix "liquid-fixpoint" liquid-fixpoint-src {};
    liquidhaskell = pkgs.haskell.lib.doJailbreak (pkgs.haskell.lib.dontCheck (self.callCabal2nix "liquidhaskell" liquidhaskell-src {}));
  });

  succinct-vector = packages: pkgs.haskell.lib.overrideCabal (packages.callCabal2nix "succinct-vector" ./. {}) (drv: {
    preCheck = ''
      export GHC_PACKAGE_PATH=$PWD/dist/package.conf.inplace/:$GHC_PACKAGE_PATH
    '';
  });

  ghc = haskellPackages.ghcWithPackages (p: with p; [
    base criterion deepseq doctest primitive QuickCheck vector (succinct-vector p)
  ]);

  liquid =
    pkgs.runCommand "liquidhaskell" { buildInputs = [ pkgs.makeWrapper ]; } ''
      mkdir -p $out/bin
      ln -s ${haskellPackages.liquidhaskell}/bin/liquid $out/bin
      wrapProgram $out/bin/liquid --prefix PATH : ${pkgs.z3}/bin
    '';

in
  pkgs.mkShell {
    buildInputs = [ liquid ghc ];
    shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
  }
