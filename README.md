```
docker build -t chor-checker .
winpty docker run --rm -p 3000:3000 --name chor-checker -it chor-checker
```