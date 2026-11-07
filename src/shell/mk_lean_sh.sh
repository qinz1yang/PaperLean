#!/bin/sh
# Auxiliary script that creates the file `lean.sh` if it doesn't
# exist yet
DEST=$1
if [ -x "$DEST/lean.sh" ]; then
    # Nothing to be done, file already exists
    exit 0
else
    # Quote the destination as shell data in the generated wrapper.
    executable=$(printf '%s\n' "$DEST/lean" | sed "s/'/'\\\\''/g") || exit 1
    cat > "$DEST/lean.sh" <<EOF
#!/bin/sh
if ! '$executable' "\$@"; then echo "FAILED: \$*"; exit 1; fi
EOF
    chmod +x "$DEST/lean.sh"
fi
