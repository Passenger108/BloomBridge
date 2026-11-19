# contrib/sjbloom/Makefile
#
# Builds the sjbloom extension: semijoin filters (Bloom filter, exact key
# list, pass-everything) that site A builds and site B tests, so that
# postgres_fdw only fetches the remote rows that can join.
#
# It builds two ways, like every contrib module:
#   inside the PostgreSQL tree:  make -C contrib/sjbloom install
#   against an installed server: make -C contrib/sjbloom USE_PGXS=1 install

MODULE_big = sjbloom
OBJS = \
	$(WIN32RES) \
	bloom.o \
	costmodel.o \
	sjb_cost.o \
	sjbloom.o

EXTENSION = sjbloom
DATA = sjbloom--1.0.sql
PGFILEDESC = "sjbloom - semijoin filters for postgres_fdw"

REGRESS = sjbloom_filter sjbloom_cost

ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/sjbloom
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif

# Make does not know that the .c files include sjb_filter.h and
# costmodel.h. Without this
# line, changing the header (for example SJB_VERSION) would not rebuild
# them, and the library would silently keep the old values.
$(OBJS): sjb_filter.h costmodel.h
