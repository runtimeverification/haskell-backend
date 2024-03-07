Compile with

```
$ ghc -O2 -package bytestring -package transformers -package containers EatSimplificationLogs.hs
```

Use like this:

```
$ ./EatSimplificationLogs < my-log-file.log > my-log-file.output
```
