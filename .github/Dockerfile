FROM rocq/rocq-prover:9.2.0-ocaml-4.14.2-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

# The base image already has `rocq-released' configured (at the pre-rename URL),
# so the repository has to be re-pointed rather than added.
#
# It also ships rocq-core 9.2.0 against rocq-stdlib 9.1.0, which is exactly the
# mismatch README.md warns about, hence the three pins.  `coq-core' is the
# compatibility-binary package: coq-menhirlib's Makefile still calls
# `coq_makefile', which the Rocq packages no longer provide.
RUN opam repository set-url rocq-released https://rocq-prover.org/opam/released \
    && opam update \
    && opam pin add -n rocq-runtime 9.2.0 \
    && opam pin add -n rocq-core 9.2.0 \
    && opam pin add -n rocq-stdlib 9.2.0 \
    && opam install rocq-runtime.9.2.0 rocq-core.9.2.0 rocq-stdlib.9.2.0 \
                    coq-core.9.2.0 menhir.20260209 rocq-equations.1.3.2+9.2 \
                    ppx_inline_test ppx_expect

# coq-menhirlib has no opam package for Rocq 9.2 yet (it still depends on the
# `coq` meta package), so build it from the matching menhir sources. The version
# must be identical to the `menhir` binary above.
RUN opam source coq-menhirlib.20260209 --dir=/tmp/menhir-20260209 \
    && make -C /tmp/menhir-20260209/coq-menhirlib all install \
    && rm -rf /tmp/menhir-20260209

# Unlike `coq' in the old coqorg image, `rocq' cannot sudo without a password,
# so the steps that install outside the opam switch run as root instead.
USER root

# docker-coq-action runs the script as `rocq' but the checkout belongs to the
# runner, so the workflow has to chown it; restore the passwordless sudo the
# coqorg images granted.
RUN printf 'rocq ALL=(ALL) NOPASSWD:ALL\n' > /etc/sudoers.d/rocq \
    && chmod 0440 /etc/sudoers.d/rocq

RUN curl -fsSLO https://gitlab.com/api/v4/projects/4207231/packages/generic/graphviz-releases/12.1.1/graphviz-12.1.1.tar.gz \
    && tar -xzf graphviz-12.1.1.tar.gz \
    && cd graphviz-12.1.1 \
    && ./configure \
    && make \
    && make install \
    && cd .. \
    && rm -rf graphviz-12.1.1.tar.gz graphviz-12.1.1

RUN apt-get update -y -q \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends pandoc \
    && rm -rf /var/lib/apt/lists/*

USER rocq
