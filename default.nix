{ overlays ? [ ], ... }@args:
import (<nixpkgs>) (args // {
  overlays = [
    (self: super:
      let
        pkgsWithEdh = super.haskellPackages.override {
          overrides = hself: hsuper: {
            edh = hself.callCabal2nix "edh" ./edh { };
            lossless-decimal =
              hself.callCabal2nix "lossless-decimal" ./lossless-decimal { };
          };
        };
      in {
        # add top-level packages
        edh = pkgsWithEdh.edh;
        lossless-decimal = pkgsWithEdh.lossless-decimal;
        # override the Haskell package set at standard locations
        haskellPackages = pkgsWithEdh;
        haskell = super.haskell // {
          packages = super.haskell.packages // { ghcWithEdh = pkgsWithEdh; };
        };
      })
  ] ++ overlays;
})
