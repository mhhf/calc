{
  description = "CALC - Proof calculus system for linear logic";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Node.js for the main project
            nodejs_22

            # Tree-sitter CLI and build requirements
            tree-sitter

            # C compiler for tree-sitter parser compilation
            gcc

            # For tree-sitter WASM builds
            emscripten

            # Useful for development
            nodePackages.npm

            # Optional: for editor integration testing
            # neovim
          ];

          shellHook = ''
            echo "CALC development environment loaded"
            echo ""
            echo "Available tools:"
            echo "  node --version     : $(node --version)"
            echo "  npm --version      : $(npm --version)"
            echo "  tree-sitter        : $(tree-sitter --version 2>/dev/null || echo 'available')"
            echo "  gcc --version      : $(gcc --version | head -1)"
            echo "  emcc               : $(emcc --version | head -1 2>/dev/null || echo 'available')"
            echo ""
            echo "Tree-sitter commands:"
            echo "  tree-sitter generate  - Generate parser from grammar.js"
            echo "  tree-sitter build     - Build native parser"
            echo "  tree-sitter build --wasm - Build WASM parser"
            echo "  tree-sitter parse <file> - Parse a file"
            echo ""
          '';

          # Environment variables for tree-sitter
          TREE_SITTER_DIR = ".tree-sitter";
        };
      }
    );
}
