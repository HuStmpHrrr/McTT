FROM rocq/rocq-prover:9.2-ocaml-4.14-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

RUN opam repo add rocq-released https://rocq-prover.org/opam/released \
    && opam update \
    && opam install rocq-equations menhir.20260209 ppx_expect \
    && eval $(opam env)

# coq-menhirlib has no opam package for Rocq 9.2 yet (it still depends on the
# `coq` meta package), so build it from the matching menhir sources. The version
# must be identical to the `menhir` binary above.
RUN eval $(opam env) \
    && opam source coq-menhirlib.20260209 --dir=/tmp/menhir-20260209 \
    && make -C /tmp/menhir-20260209/coq-menhirlib install \
    && rm -rf /tmp/menhir-20260209

RUN curl https://gitlab.com/api/v4/projects/4207231/packages/generic/graphviz-releases/12.1.1/graphviz-12.1.1.tar.gz -O \
    && tar -xzf graphviz-12.1.1.tar.gz \
    && cd graphviz-12.1.1 \
    && ./configure \
    && make \
    && sudo make install \
    && rm -rf graphviz-12.1.1.tar.gz graphviz-12.1.1

RUN sudo apt-get update -y -q \
    && DEBIAN_FRONTEND=noninteractive sudo apt-get install -y -q --no-install-recommends pandoc
