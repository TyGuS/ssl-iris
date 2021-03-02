all: benchmarks

benchmarks:
	$(MAKE) -C ints
	$(MAKE) -C dll
	$(MAKE) -C sll
	$(MAKE) -C sll-bounds
	$(MAKE) -C tree

clean:
	$(MAKE) -C ints clean
	$(MAKE) -C dll clean
	$(MAKE) -C sll clean
	$(MAKE) -C sll-bounds clean
	$(MAKE) -C tree clean