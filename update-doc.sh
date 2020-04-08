cargo doc
echo '<meta http-equiv=refresh content=0;url=graph/index.html>' > target/doc/index.html
ghp-import -n target/doc
git push origin gh-pages
