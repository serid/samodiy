{
  description = "Doge";

  nixConfig.bash-prompt-suffix = "dev$ ";

  inputs = {
    nixpkgs = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixos-22.11";
    };
  };

  outputs = { self, nixpkgs }:
    let pkgs = nixpkgs.legacyPackages.x86_64-linux; in {
      devShell.x86_64-linux = pkgs.mkShell {
        packages = [ pkgs.ghc pkgs.cabal-install pkgs.haskell-language-server ];
          # VsCode is unfree and idknow how to fix it in 
          #let vscode-haskell = 
          #  (pkgs.vscode-with-extensions.override {
          #    vscodeExtensions = with pkgs.vscode-extensions; [
          #      haskell.haskell
          #    ];
          #  }); in
          #[ vscode-haskell ];
    };
  };
}
