default: all

all: 
	agda Everything.agda

time:
	time agda Everything.agda

clean:
	find . -type f -name "*.agdai" -delete

.PHONY: default all time clean
