default: all

all: 
	agda Everything.agda

timed:
	time agda Everything.agda

clean:
	find . -type f -name "*.agdai" -delete

.PHONY: default all timed clean
