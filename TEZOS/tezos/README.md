# How to build
sudo apt-get update && sudo apt-get -y upgrade
sudo apt-get install -y curl patch unzip make gcc m4 git g++ aspcud bubblewrap libev-dev  libgmp-dev pkg-config libhidapi-dev
curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh -o install.sh
chmod 755 install.sh
sudo ./install.sh
opam init 
OPAM_VERSION=`cat scripts/version.sh | grep ocaml_version | awk -F "=" ' {print$2}'`
echo "OPAM VERSION IS" $OPAM_VERSION
opam switch create $OPAM_VERSION
eval $(opam env) && make build-deps && eval $(opam env) && make
