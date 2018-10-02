sudo cp libhidapi-libusb.so.0 /usr/lib/x86_64-linux-gnu/libhidapi-libusb.so.0
sudo apt-get install -y libev-dev
cp .tezos-client/ ~/ -rf
if [ ! -f ~/.tezos-node/identity.json ] ; then
	echo "It takes a while"
	./tezos-node identity generate
fi
cp -f ~/.tezos-node/identity.json .

