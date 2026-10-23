#!/bin/bash

dir=${1?directory unspecified}

error_out () {

    echo "$1 is not in the _CoqProject file" >&2
    exit 1
}

cd "${dir}"

# CheckAssumptions.v is checked by `make check-assumptions`, not built.
for f in `find -name '*.v' ! -path './CheckAssumptions.v'`; do
    grep -q -F "${f}" _CoqProject || error_out "${f}"
done

exit 0
