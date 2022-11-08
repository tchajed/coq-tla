#!/usr/bin/env bash

set -u

usage() {
  echo "./etc/depgraph.sh [name]" 1>&2
}

if [ $# -lt 1 ]; then
  usage
  exit 1
fi

name="$1"

# shellcheck disable=2046 # need to split into multiple arguments
coqtop $(grep '^-Q' _CoqProject) 1>/dev/null 2>coqtop.err <<EOF
From dpdgraph Require dpdgraph.
Set DependGraph File "graph.dpd".
From TLA Require examples.mutex.${name}.
Print FileDependGraph ${name}.
EOF

status="$?"
if [ $status -ne 0 ] || [ ! -f "graph.dpd" ]; then
  cat coqtop.err 1>&2
  rm coqtop.err
  exit "$status"
fi
rm coqtop.err

set -e

dpd2dot -keep-trans -without-defs \
  -graphname "$name" \
  -o graph.dot graph.dpd 1>/dev/null
dot -Tsvg -Grankdir=BT graph.dot -o"${name}.svg"
rm graph.dot graph.dpd
