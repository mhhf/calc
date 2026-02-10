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
        nodejs = pkgs.nodejs_22;

        # Build the SolidStart SSR app
        calcWeb = pkgs.buildNpmPackage {
          pname = "calc-web";
          version = "2.0.0";
          src = ./.;

          # IMPORTANT: Update this hash when dependencies change
          # Run: nix run .#update-npm-hash
          npmDepsHash = "sha256-pUWIAd5AXaPZTzCVVIrjJBf1jLqJLbHrQZE4n9fK7ZM=";

          nativeBuildInputs = [ pkgs.jq pkgs.makeWrapper ];

          # Skip native compilation - tree-sitter isn't used in the browser
          # The UI uses web-tree-sitter (WASM) instead
          npmFlags = [ "--ignore-scripts" ];
          makeCacheWritable = true;

          # Patch shebangs and create output directory for parser
          preBuild = ''
            patchShebangs libexec/
            mkdir -p out
          '';

          # Build the SolidStart SSR app
          npmBuildScript = "build";

          # Install the built server app
          installPhase = ''
            runHook preInstall

            # Create output directory structure
            mkdir -p $out/{bin,lib}

            # Copy the server output
            cp -r .output/* $out/lib/

            # Copy research docs (needed at runtime for SSR)
            mkdir -p $out/lib/dev/research
            cp -r dev/research/*.md $out/lib/dev/research/

            # Create wrapper script that sets working directory
            makeWrapper ${nodejs}/bin/node $out/bin/calc-web \
              --add-flags "$out/lib/server/index.mjs" \
              --set NODE_ENV production \
              --chdir $out/lib

            runHook postInstall
          '';

          meta = with pkgs.lib; {
            description = "CALC linear logic proof assistant - Web UI";
            license = licenses.isc;
            mainProgram = "calc-web";
          };
        };

        # Build research documentation as static HTML (fallback for static hosting)
        researchDocs = pkgs.stdenv.mkDerivation {
          pname = "calc-research";
          version = "1.0.0";
          src = ./dev/research;

          nativeBuildInputs = [ pkgs.pandoc ];

          buildPhase = ''
            mkdir -p $out

            # Create CSS for styling
            cat > $out/style.css << 'CSS'
            :root {
              --bg: #0d1117;
              --bg-secondary: #161b22;
              --text: #c9d1d9;
              --text-secondary: #8b949e;
              --link: #58a6ff;
              --border: #30363d;
              --accent: #238636;
            }
            * { box-sizing: border-box; }
            body {
              font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif;
              background: var(--bg);
              color: var(--text);
              line-height: 1.6;
              max-width: 900px;
              margin: 0 auto;
              padding: 2rem;
            }
            h1, h2, h3, h4 { color: var(--text); margin-top: 2rem; }
            h1 { border-bottom: 1px solid var(--border); padding-bottom: 0.5rem; }
            a { color: var(--link); text-decoration: none; }
            a:hover { text-decoration: underline; }
            code {
              background: var(--bg-secondary);
              padding: 0.2em 0.4em;
              border-radius: 4px;
              font-size: 0.9em;
            }
            pre {
              background: var(--bg-secondary);
              border: 1px solid var(--border);
              border-radius: 6px;
              padding: 1rem;
              overflow-x: auto;
            }
            pre code { background: none; padding: 0; }
            blockquote {
              border-left: 4px solid var(--accent);
              margin: 1rem 0;
              padding: 0.5rem 1rem;
              background: var(--bg-secondary);
            }
            table {
              border-collapse: collapse;
              width: 100%;
              margin: 1rem 0;
            }
            th, td {
              border: 1px solid var(--border);
              padding: 0.5rem 1rem;
              text-align: left;
            }
            th { background: var(--bg-secondary); }
            .nav {
              background: var(--bg-secondary);
              padding: 1rem;
              border-radius: 6px;
              margin-bottom: 2rem;
            }
            .nav a { margin-right: 1rem; }
            CSS

            # Create HTML template file
            cat > template.html << 'TEMPLATE'
            <!DOCTYPE html>
            <html lang="en">
            <head>
              <meta charset="utf-8">
              <meta name="viewport" content="width=device-width, initial-scale=1">
              <title>$title$</title>
              <link rel="stylesheet" href="style.css">
            </head>
            <body>
              <nav class="nav">
                <a href="INDEX.html">← Index</a>
                <a href="../">← CALC App</a>
              </nav>
              $body$
            </body>
            </html>
            TEMPLATE

            # Convert each markdown file to HTML
            for md in *.md; do
              name="''${md%.md}"
              echo "Converting $md..."

              # Pre-process to convert wiki links [[doc]] to HTML links, then pandoc
              sed -E 's/\[\[([^]]+)\]\]/[\1](\1.html)/g' "$md" | pandoc \
                --from=gfm \
                --to=html5 \
                --standalone \
                --css=style.css \
                --metadata title="$name - CALC Research" \
                --template=template.html \
                -o "$out/$name.html"
            done

            echo "Research docs built: $(ls -1 $out/*.html | wc -l) files"
          '';
        };

      in {
        packages = {
          default = calcWeb;
          web = calcWeb;
          research = researchDocs;
        };

        apps = {
          # Helper to update npmDepsHash
          update-npm-hash = {
            type = "app";
            program = toString (pkgs.writeShellScript "update-npm-hash" ''
              set -euo pipefail
              echo "Building to get new npm dependencies hash..."

              BUILD_OUTPUT=$(nix build .#web 2>&1 || true)

              if echo "$BUILD_OUTPUT" | grep -q "got:"; then
                NEW_HASH=$(echo "$BUILD_OUTPUT" | grep "got:" | ${pkgs.gawk}/bin/awk '{print $NF}')
              elif echo "$BUILD_OUTPUT" | grep -q "specified:.*sha256-"; then
                NEW_HASH=$(echo "$BUILD_OUTPUT" | ${pkgs.gnugrep}/bin/grep "specified:.*sha256-" | ${pkgs.gnused}/bin/sed 's/.*\(sha256-[A-Za-z0-9+/=]*\).*/\1/')
              else
                echo "Could not extract hash from build output"
                echo "$BUILD_OUTPUT"
                exit 1
              fi

              echo "Found hash: $NEW_HASH"
              ${pkgs.gnused}/bin/sed -i "s|npmDepsHash = \"sha256-[^\"]*\";|npmDepsHash = \"$NEW_HASH\";|" flake.nix
              echo "Updated flake.nix"

              nix build .#web && echo "Build successful!"
            '');
          };

          # Development server
          dev = {
            type = "app";
            program = toString (pkgs.writeShellScript "dev" ''
              export PATH="${nodejs}/bin:$PATH"
              exec npm run dev
            '');
          };

          # Run production server locally
          serve = {
            type = "app";
            program = toString (pkgs.writeShellScript "serve" ''
              export PATH="${nodejs}/bin:$PATH"
              echo "Building production server..."
              npm run build
              echo "Starting server on http://localhost:3000"
              exec node .output/server/index.mjs
            '');
          };
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            nodejs_22
            tree-sitter
            gcc
            emscripten
            nodePackages.npm
            nodePackages.typescript
            pandoc
          ];

          shellHook = ''
            echo "CALC development environment loaded"
            echo ""
            echo "Available tools:"
            echo "  node --version     : $(node --version)"
            echo "  npm --version      : $(npm --version)"
            echo "  tree-sitter        : $(tree-sitter --version 2>/dev/null || echo 'available')"
            echo ""
            echo "Commands:"
            echo "  npm run dev          # Start dev server (hot reload)"
            echo "  npm run build        # Build production server"
            echo "  npm test             # Run tests"
            echo "  nix run .#serve      # Build and run production server"
            echo "  nix run .#update-npm-hash  # Update npm hash"
            echo ""
          '';

          TREE_SITTER_DIR = ".tree-sitter";
        };
      }
    );
}
