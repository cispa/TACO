#!/bin/bash
# Replaces occurrences of http://localhost:3042 with the value of the URL 
# environment variable in the _build folder. This is necessary for sitemap.xml 
# and robots.txt to be valid when the site is generated in the CI and deployed
# via GitHub actions.

# Strict mode with error reporting
set -euo pipefail

if [ -z "$URL" ]; then
    echo "Error: URL environment variable is not set."
    echo "Usage: URL=\"https://your-domain.com\" $0"
    exit 1
fi

# Determine target directory
TARGET_DIR=""
if [ -d "docs/_build" ]; then
    TARGET_DIR="docs/_build"
elif [ -d "_build" ]; then
    TARGET_DIR="_build"
else
    echo "Error: Could not find 'docs/_build' or '_build' directory."
    exit 1
fi

echo "Target directory: $TARGET_DIR"
echo "Replacing 'http://localhost:3042' with '$URL'..."

# Find files containing the string and replace them
# grep -r: recursive
# grep -l: print filename only
# xargs -r: do not run if no input
grep -rl "http://localhost:3042" "$TARGET_DIR" | xargs -r sed -i "s|http://localhost:3042|$URL|g"

echo "Done."
