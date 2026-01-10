#!/bin/bash
set -euo pipefail

# Only run in Claude Code on the Web
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

echo "Setting up Typed Racket development environment..."

# Check if Racket is installed
if ! command -v racket &> /dev/null; then
  echo "Installing Racket..."

  # Install Racket from the official PPA
  sudo apt-get update -qq
  sudo apt-get install -y software-properties-common
  sudo add-apt-repository -y ppa:plt/racket
  sudo apt-get update -qq
  sudo apt-get install -y racket
else
  echo "Racket is already installed: $(racket --version)"
fi

# Install xvfb for GUI tests
if ! command -v xvfb-run &> /dev/null; then
  echo "Installing xvfb for GUI tests..."
  sudo apt-get install -y xvfb
fi

# Install typed-racket-test package
echo "Installing typed-racket-test package..."
raco pkg install --auto --skip-installed typed-racket-test || true

# Set up local package catalog
echo "Setting up local package catalog..."
racket -l- pkg/dirs-catalog --link --check-metadata pkgs-catalog .

# Configure package catalog
echo "file://$(pwd)/pkgs-catalog/" > catalog-config.txt
raco pkg config catalogs >> catalog-config.txt
raco pkg config --set catalogs $(cat catalog-config.txt)
rm catalog-config.txt

# Update typed-racket packages
echo "Updating typed-racket packages..."
raco pkg update --auto --no-setup \
  source-syntax/ \
  typed-racket-lib/ \
  typed-racket-more/ \
  typed-racket-compatibility/ \
  typed-racket-doc/ \
  typed-racket/ \
  typed-racket-test/ || true

# Run setup to check package dependencies
echo "Running raco setup..."
raco setup --check-pkg-deps typed typed-racket typed-racket-test typed-scheme

# Install math package for math tests
echo "Installing math package..."
raco setup math || raco pkg install --auto math

echo "✅ Typed Racket environment setup complete!"
