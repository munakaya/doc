rm -f ~/.tezos-client/blocks
./tezos-node run --bootstrap-threshold=0 --private-mode --connections=0 --net-addr=127.0.0.1:9732 --no-bootstrap-peers --rpc-addr=127.0.0.1:8732  --cors-header="content-type" --cors-origin="*"

