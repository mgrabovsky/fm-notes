.PHONY: clean

clean:
	-$(RM) *.{vo,glob,v\#} .*.aux
	-$(RM) -r .coq-native/

