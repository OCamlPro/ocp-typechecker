all:
	# ocp-build typecheck-namespace
	ocp-build typecheck

tests:
	sh make-tests.sh

clean:
	ocp-build clean

clean-tests:
	rm -f tests/*.output tests/*.diff tests/*.res tests/*~ tests/*.cm*
