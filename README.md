scsidev
=======

scsidev fork from scsidev 2.37, downloaded from
[http://www.garloff.de/kurt/linux/scsidev/]{http://www.garloff.de/kurt/linux/scsidev/}

Bugs
====

"scsidev -e" on newer kernels (3.2.26, specifically) it does not
create the /dev/scsi/sdc* devices.

FIXED: "scsidev -ye" only creates /dev/scsi/dev/sdc* devices for the
first 16 disks it finds.

