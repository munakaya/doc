read -p "Do you really want to remove all block data?(y/n)" answer
if [ $answer == "y" ] || [ $answer == "Y" ] ; then
    rm -rf ~/.tezos-node/
    rm -f ~/.tezos-client/blocks
    rm -f ~/.tezos-client/nonces
    rm -f ~/.tezos-client/wallet_lock
    mkdir ~/.tezos-node
    cp identity.json  ~/.tezos-node/
else
    echo "Cancled."
fi


