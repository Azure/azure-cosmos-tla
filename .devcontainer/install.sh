#!/bin/bash -i

## Fix issues with gitpod's stock .bashrc
cp /etc/skel/.bashrc $HOME

## Shorthands for git
git config --global alias.slog 'log --pretty=oneline --abbrev-commit'
git config --global alias.co checkout
git config --global alias.lco '!f() { git checkout ":/$1:" ; }; f'

## Waste less screen estate on the prompt.
echo 'export PS1="$ "' >> $HOME/.bashrc

## Make it easy to go back and forth in the (linear) git history.
echo 'function sn() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git show --color; }' >> $HOME/.bashrc
echo 'function n() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git checkout; }' >> $HOME/.bashrc
echo 'function p() { git checkout HEAD^; }' >> $HOME/.bashrc

## Place to install TLC, TLAPS, Apalache, ...
mkdir -p tools

## PATH below has two locations because of inconsistencies between Gitpod and Codespaces.
## Gitpod:     /workspace/...
## Codespaces: /workspaces/...

## Install TLA+ Tools (download from github instead of nightly.tlapl.us (inria) to only rely on github)
wget -qN https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -P tools/
echo "alias tlcrepl='java -cp /workspace/azure-cosmos-tla/tools/tla2tools.jar:/workspaces/azure-cosmos-tla/tools/tla2tools.jar tlc2.REPL'" >> $HOME/.bashrc
echo "alias tlc='java -cp /workspace/azure-cosmos-tla/tools/tla2tools.jar:/workspaces/azure-cosmos-tla/tools/tla2tools.jar tlc2.TLC'" >> $HOME/.bashrc

## Install CommunityModules
wget -qN https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar -P tools/

## Install TLAPS (proof system)
## No need for TLAPS for now!
#wget -N https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -P /tmp
#chmod +x /tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin
#/tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -d tools/tlaps
#echo 'export PATH=$PATH:/workspace/azure-cosmos-tla/tools/tlaps/bin:/workspaces/azure-cosmos-tla/tools/tlaps/bin' >> $HOME/.bashrc

## Install Apalache
wget -qN https://github.com/informalsystems/apalache/releases/latest/download/apalache.tgz -P /tmp
mkdir -p tools/apalache
tar xvfz /tmp/apalache.tgz --directory tools/apalache/
echo 'export PATH=$PATH:/workspace/azure-cosmos-tla/tools/apalache/bin:/workspaces/azure-cosmos-tla/tools/apalache/bin' >> $HOME/.bashrc
tools/apalache/bin/apalache-mc config --enable-stats=true

## (Moved to the end to let it run in the background while we get started)
## - graphviz to visualize TLC's state graphs
## - htop to show system load
## - texlive-latex-recommended to generate pretty-printed specs
## - z3 for Apalache (comes with z3 turnkey) (TLAPS brings its own install)
## - r-base iff tutorial covers statistics (TODO)
sudo apt-get install -y graphviz htop
## No need because Apalache comes with z3 turnkey
#sudo apt-get install -y z3 libz3-java 
sudo apt-get install -y --no-install-recommends texlive-latex-recommended
