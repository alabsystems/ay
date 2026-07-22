all: dpr-trim lpr-check compress decompress

dpr-trim: dpr-trim.c
	gcc dpr-trim.c -O2 -o dpr-trim

lpr-check: lpr-check.c
	gcc lpr-check.c -O2 -o lpr-check

compress: compress.c
	gcc compress.c -std=c99 $(FLAGS) -O2 -o compress

decompress: decompress.c
	gcc decompress.c -std=c99 $(FLAGS) -O2 -o decompress

clean:
	rm dpr-trim lpr-check compress decompress
