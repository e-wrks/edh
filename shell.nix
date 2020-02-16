# this defines the Nix env to build/run this Haskell project
with (import ./. { });
haskellPackages.edh.envFunc { withHoogle = true; }
