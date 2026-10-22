# OCaml 5.4, the version used for development: the published rocq-prover
# images for Rocq 9.2 all ship OCaml 4.14, on which driver code written against
# the newer standard library does not compile (e.g. Filename.temp_dir).  So the
# image starts from the OCaml base image and installs Rocq itself.
FROM ocaml/opam:debian-13-ocaml-5.4-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

# Rocq's packages come from its own repository, alongside the default one.
# `coq-core' is the compatibility-binary package: coq-menhirlib's Makefile still
# calls `coq_makefile', which the Rocq packages no longer provide.
RUN opam repository add rocq-released https://rocq-prover.org/opam/released --all-switches \
    && opam update \
    && opam pin add -n rocq-runtime 9.2.0 \
    && opam pin add -n rocq-core 9.2.0 \
    && opam pin add -n rocq-stdlib 9.2.0 \
    && opam install rocq-runtime.9.2.0 rocq-core.9.2.0 rocq-stdlib.9.2.0 \
                    coq-core.9.2.0 menhir.20260209 rocq-equations.1.3.2+9.2 \
                    dune ppx_inline_test ppx_expect

# coq-menhirlib has no opam package for Rocq 9.2 yet (it still depends on the
# `coq` meta package), so build it from the matching menhir sources. The version
# must be identical to the `menhir` binary above.
RUN opam source coq-menhirlib.20260209 --dir=/tmp/menhir-20260209 \
    && opam exec -- make -C /tmp/menhir-20260209/coq-menhirlib all install \
    && rm -rf /tmp/menhir-20260209

# The steps that install outside the opam switch run as root.  The base
# image's `opam' user already has passwordless sudo, which the workflow uses to
# chown the checkout.
USER root

RUN apt-get update -y -q \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends \
         pandoc python3 time pkg-config curl ca-certificates \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSLO https://gitlab.com/api/v4/projects/4207231/packages/generic/graphviz-releases/12.1.1/graphviz-12.1.1.tar.gz \
    && tar -xzf graphviz-12.1.1.tar.gz \
    && cd graphviz-12.1.1 \
    && ./configure \
    && make \
    && make install \
    && cd .. \
    && rm -rf graphviz-12.1.1.tar.gz graphviz-12.1.1

USER opam
