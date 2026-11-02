let
  f = builtins.getFlake ("path:" + toString ../.);
  p = import f.inputs.nixpkgs { system = "x86_64-linux"; };
in
p.haskell.packages.ghc912.ghcWithPackages (h: [ h.fp-ieee h.integer-roots h.statistics ])
