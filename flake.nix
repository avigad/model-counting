{
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.default = pkgs.mkShell {
        packages = with pkgs; [ 
          bashInteractive
          elan
          hyperfine
          cadical
          drat-trim
          texlive.combined.scheme-full
          texlab
          fontconfig
          (python3.withPackages (ps: with ps; [ matplotlib ]))
        ];

        FONTCONFIG_FILE = pkgs.makeFontsConf { fontDirectories = [
            "/Library/Fonts"
            "/System/Library/Fonts"
            "/Users/wojtek/Library/Fonts"
            pkgs.iosevka
          ];
        };
      };
    });
}