# this defines the Nix env to build/run this Haskell project
with (import ./. { });
haskellPackages.shellFor {
  packages = p: [ p.edh ];
  nativeBuildInputs = [ pkgs.cabal-install ];
  withHoogle = true;
}
