#!/bin/bash
python "tests/domino/programs/${1}.py" "tests/domino/programs/${1}.ll" test "tests/domino/programs/${1}.loops" ~/Downloads/cvc5-macOS
