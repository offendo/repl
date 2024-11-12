#!/bin/bash

# Define the paths
IN_DIR="test"
EXPECTED_DIR="test"

lake exe cache get > /dev/null
lake build Mathlib

# Iterate over each .in file in the test directory
for infile in $IN_DIR/*.in; do
    # Extract the base filename without the extension
    base=$(basename "$infile" .in)

    # Define the path for the expected output file
    expectedfile="$EXPECTED_DIR/$base.expected.out"

    # Check if the expected output file exists
    if [[ ! -f $expectedfile ]]; then
        echo "Expected output file $expectedfile does not exist. Skipping $infile."
        continue
    fi

    # Run the command and store its output in a temporary file
    tmpfile=$(mktemp)
    tmpfile2=$(mktemp)
    ./.lake/build/bin/repl < "$infile" | jq 'del(.commandState)' > "$tmpfile2" 2>&1
    SUM=$(jq '.tactics | length' $tmpfile2 | jq -s 'add')
    if [[ $SUM != "0" ]]; then
      jq 'del(.tactics[].extracted)' $tmpfile2 > "$tmpfile" 2>&1
    else
      cat $tmpfile2 > $tmpfile 2>&1
    fi

    # Compare the output with the expected output
    if diff <(cat $tmpfile | jq --sort-keys) <(cat $expectedfile | jq --sort-keys); then
        echo "$base: PASSED"
        # Remove the temporary file
        rm "$tmpfile"
    else
        echo "$base: FAILED"
        # Remove the temporary file
        rm "$tmpfile"
        exit 1
    fi

done

