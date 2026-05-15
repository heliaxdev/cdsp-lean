#!/usr/bin/env fish
#
# Build the Zenodo release zip. The zip file includes all tracked files (except
# git related and scripts) plus a freshly generated copy of the html documentation.

set -l repo (realpath (status dirname)/..)
set -l zip $repo/mlda-zenodo.zip
set -l tmp (mktemp -d)
set -l stage $tmp/mlda

function __release_cleanup --on-event fish_exit --on-signal INT --on-signal TERM --inherit-variable tmp
    rm -rf $tmp
end

# Regenerate documentation
mkdir -p $repo/docbuild/.lake/build/doc
touch $repo/docbuild/.lake/build/doc/references.bib
lake -d $repo/docbuild build mlda:docs
or exit 1

mkdir -p $stage
git -C $repo archive HEAD | tar -x -C $stage
rm -rf $stage/.github $stage/.gitignore $stage/scripts
cp -r $repo/docbuild/.lake/build/doc $stage/html

rm -f $zip
cd (dirname $stage); and zip -qr $zip (basename $stage)

echo "Wrote $zip"
