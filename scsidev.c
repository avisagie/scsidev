/*
 * scsidev.c 
 */

/* 
 * Program to assign static device names to SCSI devices as opposed to the
 * dynamic numbering of the Linux-1.0 -- 2.6 kernel.
 * Program written by Eric Youngdale <aric@aib.com>
 * Reworked 1/2000 Kurt Garloff <garloff@suse.de>
 * 
 * Copyright: GNU GPL.
 * Please read the file COPYING.
 *
 * Changes:
 * * 2000/01/16: Kurt Garloff <garloff@suse.de>: 
 *   - SCSI_DISK_MAJOR
 *   - Fixed lots of warnings
 *   - use tmp file in /dev/scsi
 *   Fix /etc/scsi-alias functionality
 *   - Parsing: Respect EOL \0
 *   - inquire: Request takes a few bytes, response buffer is somewhat smaller
 *		use getstr() to get and truncate strings
 *   - comparison: Empty Strings of failed inquiries do not fit
 * -> Released Version: 1.6
 * 
 * * 2000/01/17: Kurt Garloff <garloff@suse.de>:
 *   Major changes:
 *   - Now scan completely relying on sg. Does inquiry for every device
 *     immediately (it's not that expensive), and does interpret the 
 *     periph dev qualifier field to build the other high-level SCSI devs.
 *     -> removable devices will work, this way.
 *     For harddisks, the partitions will be scanned, for tapes the n version
 *     be created.
 *   Minor changes:
 *   - new inquiry () function replacing old inquire and get_version_no
 *   - added support for more than 16 SCSI disks
 *   - quiet flag -q
 *   - Link alias names flag -L
 *   - -c maxmiss option: Tolerate maxmiss missing sg devs.
 *   - rev and hostname fields
 *   - avoid unnecessary recreation of alias names
 *   - new options -n osanitize and -d elete undetected
 * -> Released Version: 2.0
 * 
 * * 2000/01/18: Kurt Garloff <garloff@suse.de>
 *   In principal, there is a chance to fool scsidev: Remove a device with
 *   a low SCSI ID and reinsert another device. Then the assumptions of
 *   scsidev about the dev no. ordering of the kernel are wrong.
 *   - Add a check for this
 *   - infrastructure changes: scsiname () and oldscsiname ()
 *   - struct regnames (sname) now has generic pointer to allow
 *     relationships between devs. name is the full name, now.
 * 
 *  * 2000/07/15: Kurt Garloff <garloff@suse.de>
 *    - Open device nodes (but sg) with O_NONBLOCK; unfortunately this is not
 *      honoured by most of Linux' SCSI high-level drivers :-(
 *    - Add support for OnStream tapes (osst)
 *  -> Version 2.20
 * 
 *  * 2000/09/04: Kurt Garloff <garloff@suse.de>
 *    - Bugfix for long hostnames from Doug Gilbert (=> 2.21)
 *    - Fix parsing of scsi.alias file: Broke on missing LF at the end
 *  -> 2.22
 * 
 *  * 2002/07/26: Kurt Garloff <garloff@suse.de>
 *    - optional (-e) cbtu naming scheme
 *    - bugfix WRT alias handling of subdevices (parititons, non-rew. tap)
 *    - Support for large SCSI IDs and LUNs. (from MGE)
 *    - Support WWID (INQ EVPD 0x83) report + aliases
 *    - Fix hex number parser
 *  -> 2.23
 * 
 *  * 2002/07/29: Kurt Garloff <garloff@suse.de>
 *    - More sane way of storing permissions
 *    - Less relying on major numbers
 *    - Support many SDs (only up to 255 that is)
 *    - Support for SCSI changers
 *  -> 2.24
 *
 *  * 2002/07/30: Kurt Garloff <garloff@suse.de>
 *    - Support for /proc/scsi/scsi extensions
 *    - Get other info from proc as well (hostname, ioport, partitions) 
 *	as needed
 *    - Alternatively match short hostname
 *    - Support for really large no of disks
 *    - Strip leading and trailing spaces for SCSI INQUIRY stuff, esp. 
 *	the serial number.
 *    - We now have a sane way of handling permission. Major code cleanup.
 *	Permissions are stored in /dev/scsi/.shadow.XXX files, now.
 *    - If working in symlink mode, we do adjust the permissions of the
 * 	underlying real dev node now.
 *  -> 2.25
 * 
 *  * 2002/08/07: Kurt Garloff <garloff@suse.de>
 *    - Fix segfault for failed inquiries
 *    - Explicitly set alias device types (could be wrong)
 *    - Check blk vs. chr devtype when updating dev node
 *  -> 2.26
 * 
 *  * 2002/08/07: Kurt Garloff <garloff@suse.de>
 *    - Fix usage message
 *  -> 2.27
 * 
 *  * 2002-10-04: Kurt Garloff <garloff@suse.de>
 *    - Bugfix from Olaf Hering (don't use arg twice in sscanf)
 *    - Multipathing support
 *    - Fix Medium Changer (and other device types with spaces) detection 
 *  -> 2.28
 * 
 *   * 2003-01-13: Kurt Garloff <garloff@suse.de>
 *     - Handle EOF return value from sscanf()
 *     - Handle empty names gracefully (for zfcp, from Bernd Kaindl)
 *   * 2003-03-07: Kurt Garloff <garloff@suse.de>
 *     - Fix symlinks to partitions (patch from Suresh Grandhi 
 *	 <Sureshg@ami.com>)
 *   * 2003-06-29: Kurt Garloff <garloff@suse.de>
 *     - Fix fd leak (/proc/partitions)
 *   -> 2.29
 *
 *   * 2003-07-25: Kurt Garloff <garloff@suse.de>
 *     - Documentation: -pX and n automatically created for aliases
 *       (Thx to Russel Shaw for suggesting it.)
 *
 *   * 2003-03-03: Evan Felix <evan.felix@pnl.gov>:
 *     - Detect HP HSV controllers and grab OS Unit ID.
 *     - Add Alias support for HSV OS Unit ID.
 *     - Changed so we search for a matching HCTL pair 
 *	 so we skip 'ghost' scsi disks which are common with 
 *	 and HSV failover pair
 *
 *   * 2003-08-07: Kurt Garloff <garloff@suse.de>:
 *     - Optionally support 'scd' instead of 'sr' as old name for
 *	 CD-ROM devices. Option -o. Relevant in symlink mode.
 *     - Add safe_strcmp() to avoid crashing in null pointers in
 *	 name (model, ...) comparisons. Thanks to James Budworth
 *	 for reporting the error.
 *
 *   * 2003-08-08: Kurt Garloff <garloff@suse.de>:
 *     - Reorder list of modules in trigger_module_loads ():
 *       In 2.6, we don't attach sg in case another driver can
 *       be attached. Thus load sg as last module.
 *     - Fix -o option
 *     - Use sysfs to gather some information (short hostname,
 *	 attached HL device -- unfortunately only block devs
 *	 currently)
 *     - Fix HSV OS ID gathering: Set to -1 if no HSV.
 *     - Handle empty model name in get_hsv_os_id().
 *   -> 2.30
 *
 *   * 2003-08-13: Kurt Garloff <garloff@suse.de>:
 *     - Brian Keefer pointed out that the symlink mode still does not
 *       work for partitions. I somehow forgot to really commit the
 *       fix from 2003-03-07.
 *   -> 2.31
 *
 *   * 2004-02-09: Kurt Garloff <garloff@suse.de>:
 *     - /sys/class/scsi_host/hostX/device/name is gone
 *       use /sys/call/scsi_host/hostX/name and/or proc_name instead.
 *     - Correctly extract dev maj:min as decimal values from sysfs
 *     - sg devices can now be found in sysfs, handle
 *   -> 2.32
 *     
 *   * 2004-02-10: Kurt Garloff <garloff@suse.de>:
 *     - Hannes Reineke found a bug that could result in creating devices
 *       with the wrong type (block vs. char).
 *     - Another patch from Hannes adding support for ASCII T10 data in
 *       page EVPD INQUIRY page 0x83.
 *     - dumppage() was using the wrong field to determine the length.
 *     - check association in page 0x83 to be for the device (Pat Mansfield)
 *     
 *   * 2004-02-16: Kurt Garloff <garloff@suse.de>:
 *     - Fix quiet option (Ulli Horlacher + /me)
 *     - Allow alternative location of scsi.alias file (-A, Ulli Horlacher)
 *     - Fix ASCII T10 data retrieval from EVPD INQ 0x83.
 *     - Fix assumption about minor being only 8bit.
 *     - Increase max length of hostname from 64 to 160. (Wolfgang Celeda)
 *   -> 2.33     
 *
 *   * 2004-03-22: Kurt Garloff <garloff@suse.de>:
 *     - Allow to switch off sysfs for debugging (-y)
 *   * 2004-03-31: Kurt Garloff <garloff@suse.de>: 
 *     - Make sure /dev/scsi/testdev is removed always.
 *     - Don't overwrite scsi device type when getting serial no. etc. in 
 *       fill_in_proc()
 *   -> 2.34.
 *
 *   * 2004-05-24: Chris Townsend <Chris_Townsend@dra-hq.com>
 *     - Fix bug with channel specified in scsi.alias
 *   * 2004-06-09: Kurt Garloff <garloff@suse.de>
 *     - Handle longer partition names
 *   -> 2.35.
 *
 *   * 2005-05-14: Kurt Garloff <garloff@suse.de>
 *     - For 2.4, search for more devices when finding matching sd dev.
 *
 *   * 2005-07-15: Nathanael Burton <mathrock@airpost.net>
 *     - When creating the non-rewinding tape device, the symlink
 *       mode failed due to a missing oldscsiname(spnt1).
 * 
 *   * 2005-08-16: Kurt Garloff <garloff@suse.de>
 *     - The 2.6 kernel now reports the 'RAID' type.
 *     - Cleanup sysfs parsing.
 *     - 2.6 tape support. (Thanks to David Chen <david@global.com>!)
 *     - SG_IO support.
 *     - Improve ID parsing (page 0x83), support EUI64 and NAA (mostly)
 *   -> 2.36
 *   
 *   * 2007-07-19: Kurt Garloff <garloff@suse.de>
 *     - Support the new sysfs names for 2.6.18+
 *   -> 2.37     
 *
 *   * 2013-02-27: Put on github.
 *
 *     TODO:
 *           Change wwid to string type to handle T10 ...
 *           handle more identifiers to match devices
 *
 */

#include <stdio.h>
//#include <linux/fs.h>
#include <sys/sysmacros.h>
#include <fcntl.h>
#include <linux/major.h>
#include <sys/stat.h>
#include <dirent.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <netinet/in.h>
#include <scsi/scsi_ioctl.h>
#include <string.h>
#include <ctype.h>
#include <getopt.h>
 
static char rcsid[] ="$Id$";
static char *versid = "scsidev " VERSION " 2007-07-19";
static char *copyright = "Copyright: GNU GPL  (see file COPYING)\n" \
" (w)  1994--1997 Eric Youngdale <eric@andante.org>\n"\
"      2000--2005 Kurt Garloff   <garloff@suse.de>";


#include "config.h"

#ifdef HAVE_SCSI_SCSI_H					/* { */
# include <scsi/scsi.h>
#else							/* } { */
# ifdef HAVE_LINUX_SCSI_H				/* { */
#  include <linux/scsi.h>
# else							/* } { */
#  ifdef HAVE__USR_SRC_LINUX_DRIVERS_SCSI_SCSI_H 	/* { */
#   include "/usr/src/linux/drivers/scsi/scsi.h"
#  else							/* } { */
#   error "Unable to include scsi.h"
#  endif						/* } */
# endif							/* } */
#endif							/* } */

/* SG_IO */
#ifdef HAVE_SCSI_SG_H
# include <scsi/sg.h>
#endif

int use_symlink = 0;
int use_scd = 0;
int symlink_alias = 0;
int filemode = 0600;
int verbose = 0;
int quiet = 0;
int maxmiss = 8;
int force = 0;
int san_del = 0;
int no_san = 0;
int no_procscsi = 0;
int no_sysfs = 0;
int full_scan = 32;
int nm_cbtu = 0;
int supp_rmvbl = 0;
int supp_multi = 0;
int override_link_perm = 1;
char *no_serial = "No serial number";
char *scsialias = "";
const unsigned long long no_wwid = 0;
const int no_hsv_os_id = -1;

#define DEVSCSI "/dev/scsi"
#define TESTDEV DEVSCSI "/testdev"
#define PROCSCSI "/proc/scsi/scsi"
#define SHADOW ".shadow."

enum devtype_t { NONE=0, SG, SD, SR, ST, OSST, SCH, };
char* devtp_nm[] = { "", "Generic", "Disk", "Rom", "Tape", "OnStreamTape", "Changer", };
char* devtp_nm26[] = { "", "sg", "sd.", "sr", "st", "osst", "sch", };

/*
 * This program builds entries in /dev/scsi that have names that are tied
 * to the actual device number and lun.   This is pretty solid as long as
 * you have only one scsi controller, but with multiple scsi controllers
 * this all falls down.  The problem is that you can have multiple controllers
 * from one manufacturer, so it is not sufficient to assign an id based upon
 * an index from the driver.  Currently the controller numbers are just the
 * internal index that is assigned by the kernel.
 *
 * A better solution would be for the kernel to assign id numbers for each
 * controller type, and the we could assign numbers based upon the number
 * of the controller located.  This would guarantee that we could generate
 * useful number.
 */

typedef struct regnames
{
    struct regnames * next;
    char * name;
    char * oldname;
    char * manufacturer;
    char * model;
    char * rev;
    char * serial;
    unsigned long long wwid;
    int  hsv_os_id;
    enum devtype_t devtp;
    char inq_devtp;
    char rmvbl;
    char unsafe;
    signed char partition;
    int  hostid;
    int  major;
    int  minor;
    char * hostname;
    char * shorthostname;
    int  hostnum;
    int  chan;
    int  id;
    int  lun;
    struct regnames * alias; // TBR
    struct regnames * related;
} sname;

/* The related pointer is new: For disks, tapes and CDRoms it points to
 * the corresponding generic sname; for generic entries, it points to
 * ZERO or to a disk/CDrom/tape */

sname * reglist = NULL;

void build_special();
int inquiry (int, sname *);
int get_hsv_os_id(int, sname *);

#ifndef SCSI_CHANGER_MAJOR
# define SCSI_CHANGER_MAJOR 86
#endif

#ifndef OSST_MAJOR
# define OSST_MAJOR 206
#endif

#define OSST_SUPPORTS(spnt) (! ( memcmp (spnt->manufacturer, "OnStream", 8) || \
			       ( memcmp (spnt->model, "SC-", 3) && \
				 memcmp (spnt->model, "DI-", 3) && \
				 memcmp (spnt->model, "DP-", 3) && \
				 memcmp (spnt->model, "FW-", 3) && \
				 memcmp (spnt->model, "USB", 3) ) ) )


enum devtype_t inq_devtp_to_devtp (const char inq_devtp, const sname *spnt)
{
	switch (inq_devtp) {
	    case TYPE_DISK:
	    case TYPE_MOD:
		return SD;
		
	    case TYPE_TAPE:
		if (spnt && OSST_SUPPORTS(spnt)) 
			return OSST;
		else
			return ST;
		
	    case TYPE_ROM:
	    case TYPE_WORM:
		return SR;
		
	    case TYPE_MEDIUM_CHANGER:
		return SCH;
		
	    default:
		return SG;
	}
}

inline char isblk (enum devtype_t devtp)
{
	switch (devtp) {
	    case SD:
	    case SR:
		return 1;
	    default:
		return 0;
	}
}

enum devtype_t nm26_to_devtp (char* nm)
{
	enum devtype_t i;
	for (i = NONE; i <= SCH; ++i) {
		const char* dtp = devtp_nm26[i];
		int ln;
		if (!strcmp (dtp, nm))
			return i;
		ln = strlen(dtp);
		if (dtp[ln-1] == '.' &&
		    !memcmp(dtp, nm, ln-1))
			return i;	
	}
	return 0;
}

/*
 * Used to maintain a list of the nodes that we have seen
 * which we know to be OK and active.
 */

void dumpentry (sname * pnt)
{
	printf ("%s (%s): %s %s %s (%s) %Lx (%d)\n", pnt->name, pnt->oldname,
		pnt->manufacturer, pnt->model, pnt->rev, pnt->serial,
		pnt->wwid, pnt->hsv_os_id);
	printf ("  on %s (%d-%x) \"%s\":\n c%di%dl%d", pnt->shorthostname,
		pnt->hostnum, pnt->hostid, pnt->hostname, pnt->chan, pnt->id, pnt->lun);
	if (pnt->devtp == SD && pnt->partition != -1)
		printf ("p%d", pnt->partition);
	printf (" %c %03x:%05x ", (isblk(pnt->devtp)? 'b': 'c'),
		pnt->major, pnt->minor); 
	printf (" SCSI %s\n", devtp_nm[(int)pnt->devtp]);
}
	

void dumplist ()
{
	sname * spnt;
	for (spnt = reglist; spnt; spnt = spnt->next)
		dumpentry (spnt);
}

/// Creates a dup scsi device registration, and a link from new to old
sname * sname_dup (sname * spnt)
{
	sname * spnt1 = malloc (sizeof (sname));
	memcpy (spnt1, spnt, sizeof (sname));
	spnt1->related = spnt; //spnt->related = spnt1;
	//spnt1->next = reglist; reglist = spnt1;
	return spnt1;
}

int safe_strcmp (const char* str1, const char* str2)
{
	if (str1 == 0 && str2 == 0)
		return 0;
	else if (str1 == 0 && str2 != 0)
		return -256;
	else if (str1 != 0 && str2 == 0)
		return 256;
	else return strcmp (str1, str2);
}

/// compare two sname entries
char sname_cmp (sname *sp1, sname *sp2)
{
    // Host
    if (sp1->hostid != sp2->hostid || 
	sp1->hostnum != sp2->hostnum) return 1;
    if (safe_strcmp (sp1->hostname, sp2->hostname)) return 1;
    // Channel, ID, LUN
    if (sp1->chan != sp2->chan) return 2;
    if (sp1->id != sp2->id) return 3;
    if (sp1->lun != sp2->lun) return 4;
    // Compare INQUIRY DATA
    if (sp1->inq_devtp != sp2->inq_devtp ||
	sp1->rmvbl != sp2->rmvbl) return 5;
    // FIXME: Don't compare devtp??
    if (safe_strcmp (sp1->manufacturer, sp2->manufacturer)) return 6;
    if (safe_strcmp (sp1->model, sp2->model)) return 7;
    if (safe_strcmp (sp1->rev, sp2->rev)) return 8;
    if (safe_strcmp (sp1->serial, sp2->serial)) return 9;
    if (sp1->wwid != sp2->wwid) return 10;
    if (sp1->hsv_os_id != sp2->hsv_os_id) return 11;
    return 0;
}

/// Used for alias registration 
sname * register_dev (char * name, int major, int minor, enum devtype_t devtp,
		      int hnum, int hid, int chan, int id,
		      int lun, int part, char * hostname, 
		      char* oldname, sname * alias, sname * rel)
{
    sname * spnt;
    //char * pnt;

    spnt = (sname *) malloc (sizeof (sname));
    //pnt = strrchr (name, '/');
    //spnt->name = strdup (pnt + 1);
    spnt->name = strdup (name);
    if (oldname) {
	if (!memcmp (oldname, "/dev/", 5))
	    spnt->oldname = strdup (oldname + 5);
	else
	    spnt->oldname = strdup (oldname);
    }
    spnt->partition = part;
    spnt->major = major;
    spnt->minor = minor;
    spnt->devtp = devtp;
    spnt->hostnum = hnum;
    spnt->hostid = hid;
    spnt->chan = chan;
    spnt->id = id;
    spnt->lun = lun;
    if (hostname) 
	spnt->hostname = strdup (hostname); 
    else 
	spnt->hostname = 0;
    spnt->alias = alias;
    spnt->related = rel;
    /*
     * Initialize this - they may be needed later.
     */
    spnt->model = spnt->manufacturer = spnt->serial = spnt->rev = NULL;
    spnt->wwid = no_wwid;
    spnt->hsv_os_id = no_hsv_os_id;
    spnt->next = reglist; reglist = spnt;
    return spnt;
}

// Creates a /dev/scsi name from the info in sname
char * scsiname (sname *spnt)
{
    char nm[64]; char *genpart;
    char app[8];
    char *dnm = 0;
    enum devtype_t tp = spnt->devtp;

    *app = 0;
    strcpy (nm, DEVSCSI); strcat (nm, "/");
    /* FIXME */
    switch (tp) {
	case SG:
	    dnm = "sg"; break;
	case SR:
	    dnm = "sr"; break;
	case ST:
	    if (spnt->minor & 0x80) 
		dnm = "nst";
	    else
		dnm = "st";
	    break;
	case OSST:
	    if (spnt->minor & 0x80) 
		dnm = "nosst";
	    else 
		dnm = "osst";
	    break;
	case SD:
	    dnm = "sd";
	    if (spnt->minor & 0x0f) 
		sprintf (app, "p%d", spnt->minor & 0x0f);
	    break;
	case SCH:
	    dnm = "sch";
	    break;
	default:
	    fprintf (stderr, "scsidev: PANIC: Illegal major 0x%03x!\n",
		     spnt->major);
	    abort ();
    }
    strcat (nm, dnm);
    genpart = nm + strlen (nm);
    if (nm_cbtu) 
	sprintf (genpart, "c%db%dt%du%d",
		 spnt->hostnum, 
		 spnt->chan, spnt->id, spnt->lun);
    else
	sprintf (genpart, "h%d-%xc%di%dl%d",
		 spnt->hostnum, spnt->hostid,
		 spnt->chan, spnt->id, spnt->lun);
    if (*app) 
	strcat (genpart, app);
    spnt->name = strdup (nm);
    return spnt->name;
}

/* Fortunately those are only needed for symlink mode
 * and if there's no exteneded /proc/scsi/scsi  KG. 
 */
int sd_major_to_disknum (const int major, const int minor)
{
	if (major == SCSI_DISK0_MAJOR)
		return minor >> 4;
	else if (major >= SCSI_DISK1_MAJOR && major <= SCSI_DISK7_MAJOR)
		return (minor >> 4) + ((major -  64) << 4);
	else if (major >= 128 && major <= 135) /* SCSI_DISK10_MAJOR -- SCSI_DISK17_MAJOR */
		return (minor >> 4) + ((major - 120) << 4);
	else if (major >= 144) /* This is only a guess :-( */
		return (minor >> 4) + ((major - 128) << 4);
	else if (major >= 72 && major < 128) /* This is only a guess :-( */
		return (minor >> 4) + ((major +  55) << 4);
	else if (major >= 136 && major < 144) /* This is only a guess :-( */
		return (minor >> 4) + ((major +  47) << 4);
	else if (major >= 12 && major <= 64) /* This is only a guess :-( */
		return (minor >> 4) + ((major + 179) << 4);
	else return -1;
}

int disknum_to_sd_major (const int diskno)
{
	int mj = diskno >> 4;
	if (mj == 0)
		return 8; /* SCSI_DISK0_MAJOR */
	else if (mj >= 1 && mj < 8)
		return 64 + mj;
	else if (mj >= 8 && mj < 16)
		return 120 + mj;
	else if (mj >= 16 && mj < 127)
		return 128 + mj;
	else if (mj >= 127 && mj < 183)
		return mj - 55;
	else if (mj >= 183 && mj < 191)
		return mj - 47;
	else if (mj >= 191 && mj < 244)
		return mj - 179;
	else return -1;
}


static void sd_devname(const unsigned int disknum, char *buffer)
{
	if (disknum < 26)
		sprintf(buffer, "sd%c", 'a' + disknum);
	else if (disknum < (26*27)) {
		unsigned int min1 = disknum / 26 - 1;
		unsigned int min2 = disknum % 26;
		sprintf(buffer, "sd%c%c", 'a' + min1, 'a' + min2);
	} else {
		unsigned int min1 = (disknum / 26 - 1) / 26 - 1;
		unsigned int min2 = (disknum / 26 - 1) % 26;
		unsigned int min3 = disknum % 26;
		sprintf(buffer, "sd%c%c%c", 'a' + min1, 'a' + min2, 'a' + min3);
	}
}


// Creates an old /dev/s? name from the info in sname
void oldscsiname (sname *spnt)
{
    char genpart[64];
    int diskno;
    enum devtype_t tp = spnt->devtp;

    switch (tp) {
	case SG:
	    sprintf (genpart, "sg%d", spnt->minor); break;
	case SR:
	    if (use_scd)
		sprintf (genpart, "scd%d", spnt->minor);
	    else
		sprintf (genpart, "sr%d", spnt->minor); 
	    break;
	case ST:
	    if (spnt->minor & 0x80) 
		sprintf (genpart, "nst%d", spnt->minor & 0x7f);
	    else
		sprintf (genpart, "st%d", spnt->minor & 0x7f);
	    break;
	case OSST:
	    if (spnt->minor & 0x80) 
		sprintf (genpart, "nosst%d", spnt->minor & 0x7f);
	    else
		sprintf (genpart, "osst%d", spnt->minor & 0x7f);
	    break;
	case SCH:
	    sprintf (genpart, "sch%d", spnt->minor);
	    break;
	case SD:
	    diskno = sd_major_to_disknum (spnt->major, spnt->minor);
	    sd_devname (diskno, genpart);
	    if (spnt->minor & 0x0f) 
		sprintf (genpart+strlen(genpart), "%d", (spnt->minor & 0x0f));
	    break;
	default:
	    fprintf (stderr, "scsidev: PANIC: Illegal device type major 0x%03x!\n",
		     spnt->major);
	    abort ();
    }
    //spnt->name = strdup (nm);
    spnt->oldname = strdup (genpart);
}


/*************************** PERMISSIONS ****************************/

/** Helper to copy perms */
inline void cp_perm (struct stat *to, const struct stat *from)
{
	to->st_uid  = from->st_uid;
	to->st_gid  = from->st_gid;
	to->st_mode = from->st_mode & ~S_IFMT;
}

/** Helper to apply perms */
inline void apply_perm (const char* nm, const struct stat *st, int fmode)
{
	chown (nm, st->st_uid, st->st_gid);
	chmod (nm, st->st_mode | fmode);
}

/** Helper to compare perms */
inline int cmp_perm (const struct stat *p1, const struct stat *p2)
{
	return (p1->st_uid  != p2->st_uid ||
		p1->st_gid  != p2->st_gid ||
		(p1->st_mode & ~S_IFMT) != (p2->st_mode & ~S_IFMT));
}

/* Construct .shadow. name */
void mk_shadow_nm (char* buf, const char* nm)
{
	const char *ptr = strrchr (nm, '/');
	*buf = 0;
	if (ptr) {
		memcpy (buf, nm, ptr-nm+1);
		buf[ptr-nm+1] = 0;
	} else
		ptr = nm;
	strcat (buf, SHADOW);
	strcat (buf, ++ptr);
}


/** Make .shadow. file for backing up permissions */
void backup_shadow (const char* nm, struct stat *stbuf)
{
	struct stat statbuf;
	char shadow[64];
	int status;
	mk_shadow_nm (shadow, nm);
	
	status = stat (shadow, &statbuf);
	if (!status && !cmp_perm (&statbuf, stbuf))
		return;
	
	if (status) {
		int fd = open (shadow, O_RDWR | O_CREAT | O_EXCL);
		close (fd);
	}
	apply_perm (shadow, stbuf, 0);
}

/** Remove the shadow file */
void rm_shadow (const char *nm)
{
	char shadow[64];
	int fd;
	mk_shadow_nm (shadow, nm);
	fd = open (shadow, O_RDONLY);
	if (fd > 0) {
		close (fd);
		unlink (shadow);
	}
}

/** Get permissions
 * Permissions:
 * (a) old permissions of nm (if it's not a symlink)
 * (b) permissions of shadow file
 * (c) permissions of file pointed to
 * (d) (new) filemode
 */
void get_perm (const char *nm, const char *linkto, struct stat * stbuf, int cdrom)
{
	int status;
	struct stat statbuf;
	char shadow[64];
	
	status = lstat (nm, &statbuf);
	if (!status && !S_ISLNK (statbuf.st_mode)) {
		cp_perm (stbuf, &statbuf);
		return;
	}
	
	mk_shadow_nm (shadow, nm);
	//printf ("%s\n", shadow);
	status = stat (shadow, &statbuf);
	
	if (!status) {
		cp_perm (stbuf, &statbuf);
		return;
	}
	
	if (linkto) {
		status = stat (linkto, &statbuf);
		if (!status) {
			cp_perm (stbuf, &statbuf);
			return;
		}
	}
	
	stbuf->st_uid = 0;
	stbuf->st_gid = 0;
	stbuf->st_mode = filemode;
	if (cdrom)
		stbuf->st_mode &= ~0222;
}
	

/**
 * Check to see if a given entry exists.  If not, create it,
 * if it does make sure the major and minor numbers are correct
 * and save permissions and ownerships (in the .shadow. file) 
 * if this is the case.
 */
void update_device (char* linkto, char * path, int fmode, int major, int minor)
{
	struct stat statbuf, statbuf2;
	int recreate;
	int newmode;
	int status;

	recreate = 0;
	get_perm (path, linkto, &statbuf2, (major == SCSI_CDROM_MAJOR));
	
	newmode = fmode | statbuf2.st_mode;
	
	status = lstat (path, &statbuf);
	if (status || S_ISLNK (statbuf.st_mode))
		++recreate;
	else if (statbuf.st_rdev != makedev (major, minor))
		++recreate;
	else if ((statbuf.st_mode & S_IFMT) != (fmode & S_IFMT))
		++recreate;
	/* Don't test permissions here, just set them later */
	if (recreate) {
		if (!status)
			unlink (path);
		status = mknod (path, newmode, makedev (major, minor));
		//printf("Recreate maj %i min %i\n", major, minor);
		if( status == -1 ) {
			fprintf (stderr, "mknod (%s) failed\n", path);
			exit (1);
		}
		apply_perm (path, &statbuf2, fmode);
	} else 
		if (cmp_perm (&statbuf, &statbuf2))
			apply_perm (path, &statbuf2, fmode);
	rm_shadow (path);
}

/** Create a symlink to the real dev */
void create_symlink (const char *linkto, const char* nm, int fmode, int major, int minor)
{
	struct stat statbuf;
	struct stat statbuf2;
	int status;
	int recreate = 0;
	
	if (!quiet) 
    		printf ("create_symlink(%s, %s, %o, %03x, %05x)\n",
		        linkto, nm, fmode, major, minor);
	get_perm (nm, linkto, &statbuf2, (major == SCSI_CDROM_MAJOR));
	
	status = lstat (nm, &statbuf);
	if (status || !S_ISLNK (statbuf.st_mode))
		++recreate;
	else {
		char realnm[64];
		int n = readlink (nm, realnm, 63);
		if (n != -1) {
			realnm[n] = 0;
			if (strcmp (linkto, realnm))
				++recreate;
		} else
			++recreate;
	}
	
	if (recreate) {
		if (!status)
			unlink (nm);
		symlink (linkto, nm);
	}
	
	/*
	 * Now make sure that the device the symlink points to 
	 * actually exists.  If not, then create that device.
	 */
	
	status = stat (linkto, &statbuf);
	if (status) {
		int newmode = statbuf2.st_mode | fmode;
		status = mknod (linkto, newmode,
				makedev (major, minor));
		fprintf (stderr, "Creating %s\n", linkto);
		apply_perm (linkto, &statbuf2, fmode);
	} else {
		if (statbuf.st_rdev != makedev (major, minor)) {
			fprintf (stderr, "scsidev: Inconsistency %s == %03x:%05x != %03x:%05x\n",
				 linkto, major(statbuf.st_rdev), minor(statbuf.st_rdev),
				 major, minor);
			abort ();
		}
		if (cmp_perm (&statbuf, &statbuf2) && override_link_perm)
			apply_perm (linkto, &statbuf2, fmode);
	}
	if (0 && override_link_perm)
		rm_shadow (nm);
	else
		backup_shadow (nm, &statbuf2);
}

/** Create device node by making symlink or calling update_device() */
void create_dev (sname *spnt, char symlink)
{
	char linkto[64];
	int devtype = isblk (spnt->devtp)? S_IFBLK: S_IFCHR;;
	strcpy (linkto, "/dev/");
	strcat (linkto, spnt->oldname);
	
	if (symlink)
		create_symlink (linkto, spnt->name, devtype, spnt->major, spnt->minor);
	else
		update_device (linkto, spnt->name, devtype, spnt->major, spnt->minor);
}


/*
 * We need to "fix" any device nodes that are currently not used because
 * it is a security risk to leave these laying around.  These are fixed
 * by storing a shadow file.  If these become active again,
 * we will be able to use them again because the minor number will be
 * set back again, and we are preserving the ownership and permissions.
 */
void sanitize_sdev ()
{
    struct dirent * de;
    char filename[64];
    DIR * sdir;
    sname * spnt;
    int status;

    /*
     * Next, delete all of the existing entries in the /dev/scsi directory.
     * The idea is that if we have added/removed devices, the numbers might have
     * changed.
     */
    sdir = opendir (DEVSCSI);
    while (1) {
	de = readdir (sdir);
	if (de == NULL) 
	    break;
	if (*de->d_name == '.')
	    continue;
	/* If it's a .shadow. name, leave it alone */
	//if (strlen (de->d_name) >= strlen (SHADOW) && !strcmp (de->d_name, SHADOW))
	//    continue;
	/*
	 * OK, we have the name.  See whether this is something
	 * we know about already.
	 */
	for( spnt = reglist; spnt; spnt = spnt->next ) {
	    if( strcmp(de->d_name, strrchr (spnt->name, '/') + 1) == 0 )
		break;
	}
	/* Didn't we find it? */
	if (spnt == NULL) {
	    struct stat statbuf;
	    strcpy (filename, DEVSCSI); strcat (filename, "/");
	    strcat (filename, de->d_name);
	    status = stat (filename, &statbuf);
	    if ( status == 0 && (S_ISLNK (statbuf.st_mode) ||
				 S_ISCHR (statbuf.st_mode) || 
				 S_ISBLK (statbuf.st_mode)) ) {
		/*
		 * OK, this one is something new that we have to do something
		 * with.  No big deal, stat it so we get the particulars, then
		 * create a new one with a safe minor number.
		 */
		unlink (filename);
		if (!san_del)
			backup_shadow (filename, &statbuf);
	    }
	}
    }
    closedir (sdir);
}


/*
 * Next, delete all of the existing entries in the /dev/scsi directory.
 * The idea is that if we have added/removed devices, the numbers might have
 * changed.
 */
void flush_sdev ()
{
	struct dirent * de;
	char filename[60];
	struct stat stbuf; 
	DIR * sdir;
	
	sdir = opendir (DEVSCSI);
	while (1) {
		de = readdir (sdir);
		if (de == NULL) 
			break;
		if (de->d_name[0] == '.')
			continue;
		//if (strlen (de->d_name >= strlen(SHADOW) && !strcmp (de->d_name+i, SHADOW))
		//	continue;
		//if (de->d_name[0] != 's' && de->d_name[0] != 'n') continue;
		strcpy (filename, DEVSCSI); strcat (filename, "/");
		strcat (filename, de->d_name);
		stat (filename, &stbuf);
		unlink (filename);
		backup_shadow (filename, &stbuf);
	}
	closedir (sdir);
	if (!quiet) 
		printf ("Flushed old " DEVSCSI " entries...\n");
	
}


/** Remove trailing whitespace */
int inline rmv_trail_ws (char* str)
{
	int i = strlen (str);
	int n = 0;
	while (--i >= 0 && (str[i] == ' ' || str[i] == '\t' || str[i] == '\n'))
		n++;
	str[i+1] = 0;
	return n;
}

/** Use ioctl to get hostnum, channel, id, lun tuple and hostid (ioport) */
int getidlun (int fd, sname *spnt, int setidlun)
{
	int status;
	int id[2];

	id[0] = 0; id[1] = 0;
	status = ioctl (fd, SCSI_IOCTL_GET_IDLUN, &id);
	
	if (status == -1)	{
		if (verbose == 2)
			fprintf (stderr, "idlun(%03x:%05x) returned %d (%d)\n",
				 spnt->major, spnt->minor, status, errno);
		close (fd);
		return -2;
	}
	
	if (setidlun) {
		/* This unfortunately limits all the numbers to be <= 255 */
		spnt->hostnum = id[0] >> 24 & 0xff;
		spnt->chan    = id[0] >> 16 & 0xff;
		spnt->lun     = id[0] >>  8 & 0xff;
		spnt->id      = id[0]       & 0xff;
	}
	spnt->hostid  = id[1];
	
	if (verbose == 2)
		fprintf (stderr, "Found %03x:%05x with idlun %08x\n", 
			 spnt->major, spnt->minor, id[0]);

	return status;
}


/** Get long scsi host adapter name by ioctl */
int getscsihostname (int fd, sname *spnt)
{
	int status;
	char hostname[160];
	*(int*)hostname = 159;
	status = ioctl (fd, SCSI_IOCTL_PROBE_HOST, hostname);
	hostname[159] = '\0';
	
	if (status == -1)	{
		if (verbose == 2)
			fprintf (stderr, "probe host (%03x:%05x) returned %d (%d)\n",
				 spnt->major, spnt->minor, status, errno);
		spnt->hostname = 0;
		return -1;
	}
	spnt->hostname = hostname? strdup (hostname): 0;
	rmv_trail_ws (spnt->hostname);
	return status;
}

/** Do hostname, idlun lookup, do inquiry and make name */
int getscsiinfo (int fd, sname *spnt, int setidlun)
{
	int status;
	
	if ((status = getidlun (fd, spnt, setidlun)))
		return status;
	if ((status = getscsihostname (fd, spnt)) < 0)
		return status;	

	status = inquiry (fd, spnt);
	get_hsv_os_id (fd, spnt);
	scsiname (spnt);
	if (setidlun)
		oldscsiname (spnt);
	return status;

}

/* Check whether disk number no matches host/chan/id/lun in spnt */
int comparediskidlun(sname *spnt, int no)
{
	int id[2];
	int scsi_id, channel, lun, host;
	int major, minor, res, fd;
	
	major = disknum_to_sd_major (no);
	minor = (no & 0x0f) << 4;
    
	res = mknod (TESTDEV, 0600 | S_IFBLK,
		makedev (major, minor));
	fd = open (TESTDEV, O_RDONLY | O_NONBLOCK);
	unlink (TESTDEV);

	if (fd < 0)
		return 0;
	res = ioctl (fd, SCSI_IOCTL_GET_IDLUN, id);
	close (fd);
	if (res < 0)
		return 0;

	host = id[0] >> 24;
	channel = (id[0] >> 16) & 0xff;
	lun = (id[0] >> 8 ) & 0xff;
	scsi_id = id[0] & 0xff;

	if (verbose >= 2) 
		printf ("Scanning: %d==%d %d==%d %d==%d %d==%d \n",
		host, spnt->hostnum, channel, spnt->chan,
		scsi_id, spnt->id, lun, spnt->lun);
	if (host == spnt->hostnum &&
	    channel == spnt->chan &&
	    scsi_id == spnt->id &&
	    lun == spnt->lun) {
		spnt->major = major;
		spnt->minor = minor;
		return 1;
	}
	return 0;
}

/* Find scsi disk high level device that points to the device
 * defined in spnt->hostnum, chan, id, lun; search all devs
 * lower than current disk no up to current+full_scan */
void findscsidisk(sname * spnt, int no) 
{
	int i;
	int searchln = no > full_scan? no: full_scan;
	if (verbose >= 1) 
		printf("Findscsidisk: %d\n",no);
	/* Default values */
	spnt->major = disknum_to_sd_major (no);
	spnt->minor = (no << 4) & ~0x0f;
	/* only search up to full_scan devices may be a bad assumption, but 
	 * scanning the whole list could take a long time */
	unlink (TESTDEV);

	if (comparediskidlun(spnt, no))
		return;
	for (i = 1; i <= searchln; ++i) {
		if (no-i >=0 && comparediskidlun(spnt, no-i))
			return;
		if (comparediskidlun(spnt, no+i))
			return;
	}               
	/* If we did not find a match, return a good guess.. */ 
	if (verbose)
		printf("No matching disk found for %i:%i:%i:%i in 0 .. %i\n",
			spnt->hostnum, spnt->chan, spnt->id, spnt->lun,
			no+searchln);
}


/* Create dev entries for a disk */
int build_disk (sname * spnt, int no)
{
    int minor; int fd; int status;
    sname * spnt1 = sname_dup (spnt);
    findscsidisk(spnt1, no);
    spnt->partition = -1;
    spnt1->devtp = SD;
    scsiname (spnt1); oldscsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
    spnt->related = spnt1;
    /* Check if device is there (i.e. medium inside) */
    fd =  open (spnt1->name, O_RDONLY | O_NONBLOCK);
    /* No access to medium / part. table */
    if (fd < 0) {
	spnt1->unsafe = 1;
	/* If it is a removable device, we can't do much more than 
	 * trusting it or not support it at all */
	if (spnt1->rmvbl && supp_rmvbl) 
	    return 0;
	fprintf (stderr, "Can't access %sremovable %s, which should "
		 "be equal to %s!\n", (spnt1->rmvbl? "": "NON-"), 
		 strrchr (spnt1->name, '/') + 1,
		 strrchr (spnt->name, '/') + 1);
	/* We don't unlink spnt1->name! Let sanitize take care of it ... */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
	
    /* Sanity checks */
    status = getscsiinfo (fd, spnt1, 1);
    close (fd);
    if (status) 
	fprintf (stderr, "scsidev: Strange: Could not get info from %s\n",
		 strrchr (spnt1->name, '/') + 1);
    if (sname_cmp (spnt, spnt1)) {
	fprintf (stderr, "scsidev: What's going on? Dev %s is different from %s\n", 
		 strrchr (spnt1->name, '/') + 1, strrchr (spnt->name, '/') + 1);
	spnt -> related = 0; spnt1 -> related = 0;
	/* And now ? */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
    /* Now do a partition scan ... */
    spnt = spnt1;
    for (minor = spnt1->minor+1; minor % 16; minor++) {
	struct stat statbuf; int status;
	status = stat (TESTDEV, &statbuf);
	if (status == 0)
	    unlink (TESTDEV);
	    
	status = mknod ( TESTDEV, 0600 | S_IFBLK,
			 makedev (spnt1->major, minor) );
	fd = open (TESTDEV, O_RDONLY | O_NONBLOCK);
	unlink (TESTDEV);
	if (fd < 0) 
	    continue;
	// TODO: Add sanity checks here ??
	close (fd);
	spnt1 = sname_dup (spnt);
	spnt1->partition = minor % 16;
	spnt1->minor = minor;
	scsiname (spnt1); oldscsiname (spnt1);
	spnt1->next = reglist; reglist = spnt1;
	create_dev (spnt1, use_symlink);
    }
    return 0;
}

int build_tape (sname * spnt, int no)
{
    int fd; int status;
    sname * spnt1 = sname_dup (spnt);
    spnt1->major = SCSI_TAPE_MAJOR;
    spnt1->minor = no;
    spnt1->devtp = ST;
    scsiname (spnt1); oldscsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
    /* Check if device is there (i.e. medium inside) */
    fd =  open (spnt1->name, O_RDONLY | O_NONBLOCK);
    if (fd < 0) {
	/* Tapes are always accessible, as they are char devices */
	fprintf (stderr, "Can't access tape %s, which should "
		 "be equal to %s!\n", strrchr (spnt1->name, '/') + 1,
		 strrchr (spnt->name, '/') + 1);
	/* We don't unlink spnt1->name! Let sanitize take care of it ... */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
    /* Do a sanity check here */
    status = getscsiinfo (fd, spnt1, 1);
    close (fd);
    if (status) 
	fprintf (stderr, "scsidev: Strange: Could not get info from %s\n",
		 strrchr (spnt1->name, '/') + 1);
    if (sname_cmp (spnt, spnt1)) {
	fprintf (stderr, "scsidev: What's going on? Dev %s is different from %s\n", 
		 strrchr (spnt1->name, '/') + 1, strrchr (spnt->name, '/') + 1);
	spnt -> related = 0; spnt1 -> related = 0;
	/* And now ? */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
    /* And create the no-rewind alias */
    spnt1 = sname_dup (spnt1);
    spnt1->minor |= 0x80;
    scsiname (spnt1); oldscsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
	
    return 0;
}

/* Create non-rew. alternative for a tape */
void create_ntape (sname * spnt)
{
	sname * spnt1 = sname_dup (spnt);
	spnt1->minor |= 0x80;
	scsiname (spnt1); oldscsiname (spnt1);
	create_dev (spnt1, use_symlink);
	spnt1->next = reglist; reglist = spnt1;
}

int build_os_tape (sname * spnt, int no)
{
    int fd; int status;
    sname * spnt1 = sname_dup (spnt);
    spnt1->major = OSST_MAJOR;
    spnt1->minor = no;
    spnt1->devtp = OSST;
    scsiname (spnt1); oldscsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
    /* Check if device is there (i.e. medium inside) */
    fd =  open (spnt1->name, O_RDONLY | O_NONBLOCK);
    if (fd < 0) {
	/* OnStream tapes are NOT always accessible, as they have a heavy open() function */
	spnt1->unsafe = 1;
	if (!quiet || !supp_rmvbl) 
	    fprintf (stderr, "Can't access tape %s, which should "
		     "be equal to %s!\n", strrchr (spnt1->name, '/') + 1,
		     strrchr (spnt->name, '/') + 1);
	if (supp_rmvbl) 
	    goto osst_force_success;
	/* We don't unlink spnt1->name! Let sanitize take care of it ... */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
    /* Do a sanity check here */
    status = getscsiinfo (fd, spnt1, 1);
    close (fd);
    if (status) 
	fprintf (stderr, "scsidev: Strange: Could not get info from %s\n",
		 strrchr (spnt1->name, '/') + 1);
    if (sname_cmp (spnt, spnt1)) {
	fprintf (stderr, "scsidev: What's going on? Dev %s is different from %s\n", 
		 strrchr (spnt1->name, '/') + 1, strrchr (spnt->name, '/') + 1);
	spnt -> related = 0; spnt1 -> related = 0;
	/* And now ? */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
 osst_force_success:
    /* And create the no-rewind alias */
    spnt1 = sname_dup (spnt1);
    spnt1->minor |= 0x80;
    scsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
	
    return 0;
}

int build_cdrom (sname * spnt, int no)
{
    int fd; int status;
    sname * spnt1 = sname_dup (spnt);
    spnt1->major = SCSI_CDROM_MAJOR;
    spnt1->minor = no;
    spnt1->devtp = SR;	
    scsiname (spnt1); oldscsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
    fd =  open (spnt1->name, O_RDONLY | O_NONBLOCK);
    /* No access to medium / part. table */
    if (fd < 0) {
	spnt1->unsafe = 1;
	/* Removable block devs are hairy! */
	if (spnt1->rmvbl && supp_rmvbl) 
	    return 0;
	fprintf (stderr, "Can't access %sremovable %s, which should "
		 "be equal to %s!\n", (spnt1->rmvbl? "": "NON-"), 
		 strrchr (spnt1->name, '/') + 1,
		 strrchr (spnt->name, '/') + 1);
	/* We don't unlink spnt1->name! Let sanitize take care of it ... */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
	
    /* Do a sanity check */
    status = getscsiinfo (fd, spnt1, 1);
    close (fd);
    if (status) 
	fprintf (stderr, "scsidev: Strange: Could not get info from %s\n",
		 strrchr (spnt1->name, '/') + 1);
    if (sname_cmp (spnt, spnt1)) {
	fprintf (stderr, "scsidev: What's going on? Dev %s is different from %s\n", 
		 strrchr (spnt1->name, '/') + 1, strrchr (spnt->name, '/') + 1);
	/* And now ? */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
    return 0;
}

int build_changer (sname * spnt, int no)
{
    int fd; int status;
    sname * spnt1 = sname_dup (spnt);
    spnt1->major = SCSI_CHANGER_MAJOR;
    spnt1->minor = no;
    spnt1->devtp = SCH;
    scsiname (spnt1); oldscsiname (spnt1);
    spnt1->next = reglist; reglist = spnt1;
    create_dev (spnt1, use_symlink);
    fd =  open (spnt1->name, O_RDONLY | O_NONBLOCK);
    /* No access to medium / part. table */
    if (fd < 0) {
	spnt1->unsafe = 1;
	/* Removable block devs are hairy! */
	if (spnt1->rmvbl && supp_rmvbl) 
	    return 0;
	fprintf (stderr, "Can't access %sremovable %s, which should "
		 "be equal to %s!\n", (spnt1->rmvbl? "": "NON-"), 
		 strrchr (spnt1->name, '/') + 1,
		 strrchr (spnt->name, '/') + 1);
	/* We don't unlink spnt1->name! Let sanitize take care of it ... */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }

    /* Do a sanity check */
    status = getscsiinfo (fd, spnt1, 1);
    close (fd);
    if (status) 
	fprintf (stderr, "scsidev: Strange: Could not get info from %s\n",
		 strrchr (spnt1->name, '/') + 1);
    if (sname_cmp (spnt, spnt1)) {
	fprintf (stderr, "scsidev: What's going on? Dev %s is different from %s\n",
		 strrchr (spnt1->name, '/') + 1, strrchr (spnt->name, '/') + 1);
	/* And now ? */
	reglist = spnt1->next; free (spnt1->name); 
	spnt->related = 0; free (spnt1);
	return 1;
    }
    return 0;
}

/* Use /proc/partitions to scan for partitions */
void create_partitions (sname * spnt)
{
	char pline[128]; char *ptr;
	FILE *pf = fopen ("/proc/partitions", "r");
	if (!pf) {
		fprintf (stderr, "scsidev: Couldn't read /proc/partitions: %s\n",
			 strerror (errno));
		return;
	}
	while (!feof (pf)) {
		unsigned int maj, min, blk;
		char nm[64], nm2[64];
		ptr = fgets (pline, 128, pf);
		if (!ptr)
			break;
		if (sscanf (pline, " %d %d %d %8s", &maj, &min, &blk, nm) < 4)
			continue;
		
		/* Strip part */
		strcpy (nm2, nm);
		if (isdigit (nm2[strlen(nm2)-1])) {
			for (ptr = nm2+strlen(nm2)-1; isdigit(*ptr); --ptr);
			*(++ptr) = 0;
		}
		ptr = nm + strlen(nm2);
		if (!strcmp (nm2, spnt->oldname)) {
			/* Found it ! */
			if (maj != spnt->major || (min & ~0x0f) != (spnt->minor)) {
				fprintf (stderr, "scsidev: Inconsistency found: /proc/partitions reports "
					 " %s as %03x:%05x\n whereas we have %03x:%05x\n",
					 nm2, maj, min & ~0x0f, spnt->major, spnt->minor);
				dumpentry (spnt);
				abort ();
			}
			if (isdigit (*ptr)) {
				int part = atoi (ptr);
				sname * spnt1 = sname_dup (spnt);
				spnt1->minor |= part; spnt1->partition = part;
				scsiname (spnt1); 
				spnt1->oldname = strdup (nm);
				create_dev (spnt1, use_symlink);
				spnt1->next = reglist; reglist = spnt1;
			}
		}
	}
	fclose (pf);
}
	


void build_sgdevlist ()
{
    int fd; 
    struct stat statbuf;
    int status;
    sname * spnt;
    int disks = 0, tapes = 0, cdroms = 0, changers = 0;
    int miss = 0;	
    int minor = 0;
    int major = SCSI_GENERIC_MAJOR; 
    int mode = O_RDWR | O_NONBLOCK;
    //    int devtype = (SCSI_BLK_MAJOR(major)? S_IFBLK: S_IFCHR);
    enum devtype_t devtp;
    
    status = stat (DEVSCSI, &statbuf);
    if (status == -1)
	return;

    status = stat (TESTDEV, &statbuf);
    if (status == 0)
	unlink (TESTDEV);

    if (verbose >= 1)
	fprintf (stderr, "Building list for sg (%s dev major %03x)\n",
		 "char", major);

    while (minor <= 255) {
	errno = 0;
	status = mknod ( TESTDEV, 0600 | S_IFCHR, 
			 makedev (major, minor) );
	if (status) { 
	    perror ("scsidev: mknod"); 
	    exit (3); 
	}
	fd = open (TESTDEV, mode);
	unlink (TESTDEV);
	if (fd == -1) {
	    if (verbose == 2)
		fprintf (stderr, "open(%03x:%05x) returned %d (%d)\n",
			 major, minor, fd, errno);
	    miss++;
	    if (miss > maxmiss) 
		break;
	    else { 
		minor++; continue; 
	    }
	}
	spnt = (sname*) malloc (sizeof (sname));
	memset (spnt, 0, sizeof (sname));
	spnt->major = major;   spnt->minor = minor;
	spnt->devtp = SG;
	spnt->name  = TESTDEV; spnt->partition = -1;
	status = getscsiinfo (fd, spnt, 1);
	close (fd);

	if (status) { 
		free (spnt); miss++;
		if (miss > maxmiss) 
		    break;
		else { 
		    minor++; continue; 
		}
	}
	//scsiname (spnt) called by getscsiinfo();

	spnt->next = reglist; reglist = spnt;
	create_dev (spnt, use_symlink);

	devtp = inq_devtp_to_devtp (spnt->inq_devtp, spnt);

	if (!quiet) 
	    printf ("Found %s (Type %02x) %c on %s \n", spnt->name,
		    spnt->inq_devtp, (spnt->rmvbl? 'R' : ' '),
		    spnt->hostname);

	/* Now register cdroms, tapes, and disks as well */
	switch (devtp) {
	    case SD:
		if (!build_disk (spnt, disks)) 
			disks++;
		/* This shouldn't happen, we search already in findscsidisk() 
		else if (!build_disk (spnt, disks+1)) 
			disks += 2;
		 */	
		break;
	    case ST:
		if (!build_tape (spnt, tapes)) 
			tapes++;
		else if (!build_tape (spnt, tapes+1)) 
			tapes += 2;
		break;
	    case OSST:
		if (!build_os_tape (spnt, tapes)) 
			tapes++;
		else if (!build_os_tape (spnt, tapes+1)) 
			tapes += 2;
		break;
	    case SR:
		if (!build_cdrom (spnt, cdroms)) 
			cdroms++;
		else if (!build_cdrom (spnt, cdroms+1)) 
			cdroms += 2;
		break;
	    case SCH:
		if (!build_changer (spnt, changers)) 
			changers++;
		else if (!build_cdrom (spnt, changers+1)) 
			changers += 2;
		break;
		
	    default:
		;/* nothing to be done */
	}
	minor += 1;
    }
    //unlink (TESTDEV);
}

char fourlnbuf[4][128];
/* Fill fourlnbuf with the next record from /proc/scsi/scsi */
int procscsi_readrecord (FILE* f)
{
	int c; char *ptr;
	fourlnbuf[0][0] = 0; fourlnbuf[1][0] = 0;
	fourlnbuf[2][0] = 0; fourlnbuf[3][0] = 0;
	do {
		ptr = fgets (fourlnbuf[0], 128, f);
		if (!ptr || feof (f))
			return -1;
	} while (memcmp (fourlnbuf[0], "Host:", 5));
	ptr = fgets (fourlnbuf[1], 128, f);
	ptr = fgets (fourlnbuf[2], 128, f);
	/* Test for extensions ... */
	c = fgetc (f);
	if (c != EOF) {
		ungetc (c, f);
		if (c != 'H') {
			ptr = fgets (fourlnbuf[3], 128, f);
			c = fgetc (f);
			if (c != EOF) 
				ungetc (c, f);
		}
	}
#ifdef DEBUG
	printf ("procscsi_readrecord:\n");
	printf ("%s", fourlnbuf[0]); printf ("%s", fourlnbuf[1]);
	printf ("%s", fourlnbuf[2]); printf ("%s", fourlnbuf[3]);
	printf ("%i\n", fourlnbuf[3][0]);
#endif
	return 0;
}

/* This is a copy of 
 * const char *const scsi_device_types[MAX_SCSI_DEVICE_CODE]
 * from linux/drivers/scsi/scsi.c
 */
#define MAX_SCSI_DEVICE_CODE 15
const char *const scsi_device_types[MAX_SCSI_DEVICE_CODE] =
{
	"Direct-Access",
	"Sequential-Access",
	"Printer",
	"Processor",
	"WORM",
	"CD-ROM",
	"Scanner",
	"Optical Device",
	"Medium Changer",
	"Communications",
	"Unknown",
	"Unknown",
	"RAID",
	"Enclosure",
	"Direct-Access-RBC",
};


char linux_to_devtp (const char* tp)
{
	int idx;
	if (!strcmp (tp, "Unknown"))
		return 0x1f;
	for (idx = 0; idx < MAX_SCSI_DEVICE_CODE; ++idx)
		if (!strcmp (tp, scsi_device_types[idx]))
			return idx;
	fprintf (stderr, "Linux kernel reports new device type \"%s\". Mail author!\n",
		 tp);
	return 0x1f;
}

/* Parse contents of fourlnbuf */
int procscsi_parse (sname *spnt)
{
	char vendor[9];
	char product[17];
	char rev[5];
	char devtype[21];
	char hldev0[16], hldev1[16], hldev2[16], hldev3[16];
	int ansi;
	
	sscanf (fourlnbuf[0], "Host: scsi%i Channel: %d Id: %d Lun: %d",
		&spnt->hostnum, &spnt->chan, &spnt->id, &spnt->lun);
	sscanf (fourlnbuf[1], "  Vendor: %8c Model: %16c Rev: %4c",
		vendor, product, rev);
	vendor[8] = 0; product[16] = 0; rev[4] = 0;
	rmv_trail_ws (vendor); rmv_trail_ws (product); rmv_trail_ws (rev);
	spnt->manufacturer = strdup (vendor);
	spnt->model = strdup (product);
	spnt->rev = strdup (rev);
	sscanf (fourlnbuf[2], "  Type: %20c ANSI SCSI revision: %d",
		devtype, &ansi);
	devtype [20] = 0; rmv_trail_ws (devtype);
	spnt->inq_devtp = linux_to_devtp (devtype);
	if (!fourlnbuf[3][0])
		return 0;
	return sscanf (fourlnbuf[3], "  Attached drivers: %16s %16s %16s %16s",
		       hldev0, hldev1, hldev2, hldev3);
}

int procscsiext_parse (sname *spnt, int idx)
{
	char hldev[4][16];
	char* hdev; char* devptr;
	char tp;
	int n = sscanf (fourlnbuf[3], "  Attached drivers: %16s %16s %16s %16s",
			hldev[0], hldev[1], hldev[2], hldev[3]);
	if (idx >= n) {
	    return -1;
	} else
		hdev = hldev[idx];
	
	for (devptr = hdev; *devptr != '(' && *devptr != 0; ++devptr);
	*devptr++ = 0;
	spnt->oldname = strdup (hdev);

	sscanf (devptr, "%c:%x:%x)", &tp, &spnt->major, &spnt->minor);
	
	// We don't use tp (which can be 'b' or 'c')
	
	if (!memcmp (hdev, "sg", 2))
		spnt->devtp = SG;
	else
		spnt->devtp = inq_devtp_to_devtp (spnt->inq_devtp, spnt);

	scsiname (spnt);	
	return 0;
}

char* find_scsihostname (int hnum)
{
	struct dirent *sde;
	DIR * sdir;
	char path[64];
	char num[8];
	char* const phost = path + strlen("/proc/scsi/");
	
	strcpy (path, "/proc/scsi/");
	sprintf (num, "/%d", hnum);
	
	sdir = opendir ("/proc/scsi");
	if (!sdir) {
		fprintf (stderr, "can't read /proc/scsi/: %s\n",
			 strerror (errno));
		abort ();
	}
	while (1) {
		int fd;
		sde = readdir (sdir);
		if (!sde)
			break;
		if (!strcmp (sde->d_name, "scsi") || *sde->d_name == '.')
			continue;
		strcpy (phost, sde->d_name);
		strcat (phost, num);
		fd = open (path, O_RDONLY);
		if (fd > 0) {
			char * nm = strdup (sde->d_name);
			close (fd);
			closedir (sdir);
			return nm;
		}
	}
	closedir (sdir);
	return 0;
}

unsigned int find_ioport (const char* nm)
{
	unsigned char lnbuf[128];
	char nm2[64]; char *nmptr;
	char * buf;
	FILE * iop = fopen ("/proc/ioports", "r");
	if (!iop)
		return 0;
	/* nm2 = to_lower (nm); */
	strcpy (nm2, nm);
	for (nmptr = nm2; *nmptr; ++nmptr)
		*nmptr = tolower (*nmptr);
	
	while (!feof (iop)) {
		unsigned int io1, io2;
		char name[64];
		buf = fgets (lnbuf, 128, iop);
		if (!buf)
			break;
		sscanf (lnbuf, " %x-%x : %s", &io1, &io2, name);
		if (!strcmp (name, "PCI"))
			continue;
		/* name = to_lower (name); */
		for (nmptr = name; *nmptr; ++nmptr)
			*nmptr = tolower (*nmptr);
		if (!strcmp (nm2, name)) {
			fclose (iop);
			return io1;
		}
	}
	fclose (iop);
	return 0;
}

char* sysfs_findhostname (sname *sdev)
{
	char buf[128]; FILE* f; char* ptr;
	strcpy (buf, "/sys/class/scsi_host/");
	sprintf (buf+strlen(buf), "host%d/", sdev->hostnum);
	ptr = buf+strlen(buf);
	strcat (buf, "unique_id");
	f = fopen (buf, "r");
	if (!f) {
		fprintf (stderr, "Could not open \"%s\"!\n", buf);
		return 0;
	}
	fscanf (f, "%i", &sdev->hostid);
	fclose (f);
	*ptr = 0;
	strcat (buf, "name");	// used to be device/name
	f = fopen (buf, "r");
	if (f) {
		char buf2[128];
		fgets (buf2, 127, f);
		if (buf2[strlen(buf2)-1] == '\n')
			buf2[strlen(buf2)-1] = 0;
		sdev->hostname = strdup (buf2);
		fclose (f);
	}
	*ptr = 0; 
	strcat (buf, "proc_name");
	f = fopen (buf, "r");
	if (!f) {
		fprintf (stderr, "Could not open \"%s\"!\n", buf);
		return 0;
	}
	fgets (buf, 127, f);
	fclose (f);
	if (buf[strlen(buf)-1] == '\n')
		buf[strlen(buf)-1] = 0;
	return strdup (buf);
}

void fill_in_proc (sname * spnt)
{
	int fd;
	spnt->shorthostname = find_scsihostname (spnt->hostnum);
	if (!spnt->shorthostname) 
		spnt->shorthostname = sysfs_findhostname (spnt);
	if (!spnt->shorthostname) {
		fprintf (stderr, "scsidev: warning: could not deduce hostname & hostid\n");
		return;
	}
	if (!spnt->hostname)
		spnt->hostname = strdup (spnt->shorthostname);
	if (!spnt->hostid)
		spnt->hostid = find_ioport (spnt->shorthostname);

	/* Don't overwrite device type! It should have been filled correctly
	 * and with matching major/minor before. */
	// spnt->devtp = inq_devtp_to_devtp (spnt->inq_devtp, spnt);/

	unlink(TESTDEV);
	fd = mknod (TESTDEV, 0600 | (isblk(spnt->devtp)? S_IFBLK: S_IFCHR),
		    makedev (spnt->major, spnt->minor));
	if (fd) {
		fprintf (stderr, "scsidev: Can't mknod " TESTDEV ": %s\n",
			 strerror (errno));
		return;
	}
	fd = open (TESTDEV, O_RDWR | O_NONBLOCK);
	unlink (TESTDEV);
	if (fd == -1) {
	    char buf[64];
            sprintf(buf, "open %s %03x:%05x",
		   isblk(spnt->devtp)? "b": "c", spnt->major, spnt->minor); 
	    perror(buf);
	    return;
	}
	inquiry (fd, spnt);
	get_hsv_os_id(fd, spnt);
	close (fd);
	//scsiname (spnt);
}
		

void fill_in_sg (sname * spnt)
{
	int status; int fd;

	errno = 0;
	unlink (TESTDEV);
	status = mknod (TESTDEV, 0600 | S_IFCHR,
			makedev (spnt->major, spnt->minor));
	if (status) { 
		perror ("scsidev: mknod"); 
		exit (3); 
	}
	fd = open (TESTDEV, O_RDWR);
	unlink (TESTDEV);
	getscsiinfo (fd, spnt, 0);
	close (fd);
	spnt->shorthostname = find_scsihostname (spnt->hostnum);
	if (spnt->hostid == 0 && spnt->shorthostname)
		spnt->hostid = find_ioport (spnt->shorthostname);
}



/* Create device nodes etc. */
void dev_specific_setup (sname * spnt)
{
	if (verbose >= 2) {
		printf ("dev_specific_setup () for %s\n",
			spnt->name);
		dumpentry (spnt);
	}
	create_dev (spnt, use_symlink);
	switch (spnt->devtp) {
	    case SG:
	    case SR:
	    case SCH:
		break;
	    case ST:
	    case OSST:
		create_ntape (spnt);
		break;
	    case SD:
		spnt->partition = -1;
		create_partitions (spnt);
		break;
	    default: 
		fprintf (stderr, "scsidev: Unset dev type! Oops!\n");
		dumpentry (spnt);
		abort ();
	}
}

/* access a dev that's unlikely to exist to trigger module loads
 * with a minimum of side effects */
void trigger_one_mod (char blk, int major, int minor)
{
	int fd;
	fd = mknod (TESTDEV, blk? S_IFBLK: S_IFCHR, makedev (major, minor));
	if (fd)
		return;
	fd = open (TESTDEV, O_RDWR | O_NONBLOCK);
	if (fd > 0)
		close (fd);
	unlink (TESTDEV);
}

void trigger_module_loads ()
{
	unlink (TESTDEV);
	/* sd */
	trigger_one_mod (1, SCSI_DISK0_MAJOR, 255);
	/* sr */
	trigger_one_mod (1, SCSI_CDROM_MAJOR, 255);
	/* osst */
	trigger_one_mod (0, OSST_MAJOR, 255);
	/* st */
	trigger_one_mod (0, SCSI_TAPE_MAJOR, 255);
	/* sch */
	trigger_one_mod (0, SCSI_CHANGER_MAJOR, 255);
	/* sg */
	trigger_one_mod (0, SCSI_GENERIC_MAJOR, 255);
}

struct sysfsdev {
	int maj, min;
	char nm[23];
	char blk;
};

struct sysfsdev sysfsdevs[2];


/* Strip /dev part from nm and readlink the device name */
void sysfs_get_dev_nm (char* nm, struct sysfsdev* sysfsdevptr)
{
	char buf[128];
	char* ptr = strrchr (nm, '/');
	int ln;
	*ptr = 0;
	ln = readlink (nm, buf, 128);
	buf[ln] = 0;
	ptr = strrchr (buf, '/');
	strcpy (sysfsdevptr->nm, ptr+1);
}

void sysfs_get_generic_nm (char* nm, struct sysfsdev* sysfsdevptr)
{
	char buf[128]; char *ptr;
	int ln;
	ln = readlink (nm, buf, 128);
	buf[ln] = 0;
	ptr = strrchr (buf, '/');
	strcpy (sysfsdevptr->nm, ptr+1);
}

FILE* sysfs_fopen_pattern(const char* basenm, const char* pat, char* nm)
{
	DIR *dir = opendir(basenm);
	struct dirent *dent;
	const ssize_t ln = strlen(pat);
	if (!dir)
		return NULL;
	while (dent = readdir(dir)) {
		if (0 == memcmp(pat, dent->d_name, ln)) {
			strcpy(nm, basenm);
			strcat(nm, dent->d_name);
			strcat(nm, "/dev");
			return fopen(nm, "r");
		}
	}
	return NULL;
}

int sysfs_read_devinfo(char* basenm, struct sysfsdev* sysfsptr, 
		       sname * spnt, char* suffix, char blk)
{
	FILE* f;
	char nm[128];
	strcpy(nm, basenm);
	strcat(nm, suffix);
	strcat(nm, "/dev");
	f = fopen(nm, "r");
	if (!f) {
		f = sysfs_fopen_pattern(basenm, suffix, nm);
		if (!f)
			return 0;
	}
	sysfsptr->blk = blk;
	fscanf(f, "%i:%i", &sysfsptr->maj, &sysfsptr->min);
	sysfs_get_dev_nm(nm, sysfsptr);
	if (verbose > 1)
		printf ("sysfs_read_devinfo %d:%d:%d:%d -> %s(%c %x:%x)\n",
			spnt->hostnum, spnt->chan, spnt->id, spnt->lun,
			sysfsptr->nm, blk? 'b': 'c',
			sysfsptr->maj, sysfsptr->min);
	fclose(f);
	return 1;
}


int sysfs_getinfo (sname * spnt)
{
	char nm[128]; 
	int dev = 0;
	int inq_devtp;
	FILE* f;

	strcpy (nm, "/sys/class/scsi_device/");
	sprintf (nm+strlen(nm), "%d:%d:%d:%d",
		 spnt->hostnum, spnt->chan, spnt->id, spnt->lun);
	strcat (nm, "/device/");
	/* sysfs devs */
	dev += sysfs_read_devinfo(nm, sysfsdevs+dev, spnt, "block", 1);
	dev += sysfs_read_devinfo(nm, sysfsdevs+dev, spnt, "tape", 0);
	dev += sysfs_read_devinfo(nm, sysfsdevs+dev, spnt, "generic", 0);
	
	strcat (nm, "type");
	f = fopen (nm, "r");
	fscanf (f, "%i", &inq_devtp);
	spnt->inq_devtp = inq_devtp;
	/* TODO: Use much more info from sysfs, e.g. driver */
	fclose (f);
	
	return dev;
}	

void sysfs_parse (sname *spnt, int idx)
{	
	char nm[23];
	char *p1 = sysfsdevs[idx].nm, *p2 = nm;
	
	while (!isdigit(*p1) && *p1)
		*p2++ = *p1++;
	*p2 = 0;
	spnt->oldname = strdup(sysfsdevs[idx].nm);
	spnt->major   = sysfsdevs[idx].maj;
	spnt->minor   = sysfsdevs[idx].min;
	//spnt->blk     = sysfsdevs[idx].blk;
	/* Note: We need to handle generic here, thus can't rely on inq_devtp */
	//spnt->devtp   = inq_devtp_to_devtp(spnt->inq_devtp, spnt);
	spnt->devtp   = nm26_to_devtp(nm);

	if (verbose >= 1) {
		dumpentry(spnt);
		printf("Names %s, %s\n", spnt->oldname, nm);
	}
	scsiname(spnt);
}
	

/* Build device list by reading /proc/scsi/scsi with extensions from scsi-many or sysfs */
void build_sgdevlist_procscsi ()
{
	FILE* scsifile;
	sname * spnt;
	int status;
	struct stat statbuf;
	int rdevs = 0, hdevs = 0;

	status = stat (DEVSCSI, &statbuf);
	if (status == -1)
		return;

	status = stat (TESTDEV, &statbuf);
	if (status == 0)
		unlink (TESTDEV);
	
	if (verbose >= 1)
		fprintf (stderr, "Building device list using " PROCSCSI "\n");
	
	scsifile = fopen (PROCSCSI, "r");
	if (!scsifile) {
		fprintf (stderr, "scsidev: could not open " PROCSCSI ": %s\n",
			 strerror (errno));
		return;
	}
	fclose (scsifile);
    
	scsifile = fopen (PROCSCSI, "r");
	/* parse /proc/scsi */
	while (!feof (scsifile)) {
		int hl_per_dev; int hl;
		sname *sgpnt = 0;
		if (procscsi_readrecord (scsifile))
			break;
		++rdevs;
		spnt = malloc (sizeof (sname));
		memset (spnt, 0, sizeof (sname));
		hl_per_dev = procscsi_parse (spnt);
		if (!hl_per_dev || hl_per_dev == EOF) 
			hl_per_dev = sysfs_getinfo (spnt);
		if (!hl_per_dev || hl_per_dev == EOF) {
			free (spnt);
			fprintf (stderr, "Low level dev without HL driver?\n");
			continue;
		}
		spnt->next = reglist; reglist = spnt;
		if (verbose > 1)
			printf ("dev %d:%d:%d:%d: %i drivers\n",
				spnt->hostnum, spnt->chan, spnt->id, spnt->lun,
				hl_per_dev);
		for (hl = 0; hl < hl_per_dev; ++hl) {
			if (hl) {
				spnt = sname_dup (spnt);
				spnt->next = reglist; reglist = spnt;
				spnt->major = 0;
			}
			++hdevs; spnt->partition = -1;
			procscsiext_parse (spnt, hl);
			if (spnt->major == 0)
				sysfs_parse (spnt, hl);
			if (spnt->devtp == SG)
				sgpnt = spnt;
		}
		/* Fill in missing information (inquiry, host adapter name ...) */
		if (sgpnt)
			fill_in_sg (sgpnt);
		if (!spnt->shorthostname)
			fill_in_proc (spnt);
		if (!sgpnt)
		    sgpnt = spnt;
		/* Copy info to the colleagues
		 * and do special stuff depending on dev types. Such as the non-rew.
		 * variant for tapes or the partitions on disks
		 */
		for (hl = 0; hl < hl_per_dev; ++hl, spnt = spnt->next) {
			if (spnt != sgpnt) {
				if (sgpnt->serial) 
					spnt->serial = strdup (sgpnt->serial);
				spnt->wwid = sgpnt->wwid;
				spnt->rmvbl = sgpnt->rmvbl;
				//spnt->unsafe = sgpnt->unsafe;
				spnt->hostid = sgpnt->hostid;
				if (sgpnt->hostname)
					spnt->hostname = strdup (sgpnt->hostname);
				if (sgpnt->shorthostname) 
					spnt->shorthostname = strdup (sgpnt->shorthostname);
				spnt->related = sgpnt;
			}
#if 1
			/* This does the handling of the dev nodes */
			dev_specific_setup (spnt);
#endif
		}
	}
	if (verbose >= 1) {
		printf ("%i real SCSI devices found, %i high level devs attached\n",
			rdevs, hdevs);
		dumplist ();
	}
}
	

/* Test for availability of /proc/scsi/scsi extensions */
int procscsi_ext_status ()
{
	int n;
	FILE *f = fopen (PROCSCSI, "r");
	if (!f) {
		fprintf (stderr, "scsidev: " PROCSCSI " does not exist?\n");
		return 0;
	}
	n = procscsi_readrecord (f);
	fclose (f);
	/* We don't know ... */
	if (n < 0)
		return 1;
	if (fourlnbuf[3][0])
		return 1;
	else
		return 0;
}

/* Try to switch on extensions */
int procscsi_ext_on ()
{
	FILE *f = fopen (PROCSCSI, "w");
	if (!f) {
		fprintf (stderr, "scsidev: " PROCSCSI ": %s\n",
			 strerror (errno));
		return -1;
	}
	fprintf (f, "scsi report-devs 1\n");
	fclose (f);
	//fprintf (stderr, "Switched on " PROCSCSI " extensions\n");
	return 0;
}

/* Try to switch on extensions */
int procscsi_ext_off ()
{
	FILE *f = fopen (PROCSCSI, "w");
	if (!f) {
		fprintf (stderr, "scsidev: " PROCSCSI ": %s\n",
			 strerror (errno));
		return -1;
	}
	fprintf (f, "scsi report-devs 0\n");
	fclose (f);
	//fprintf (stderr, "Switched off " PROCSCSI " extensions\n");
	return 0;
}


int try_procscsi ()
{
	int se_status = procscsi_ext_status();
	if (!se_status)
		procscsi_ext_on();
	if (!procscsi_ext_status())
		return -1;
	
	build_sgdevlist_procscsi(0);
	
	if (!se_status)
		procscsi_ext_off();
	return 0;
}



/* Try sysfs */
int find_sysfs ()
{
	DIR *sdev_dir = opendir("/sys/class/scsi_device");
	if (!sdev_dir)
		return -1;
	closedir (sdev_dir);
	build_sgdevlist_procscsi(1);
	return 0;
}


void usage()
{
    fprintf (stderr, "%s\n", versid);
    fprintf (stderr, "Usage: scsidev [options]\n");
    fprintf (stderr, " -f     : Force deletion of all " DEVSCSI" entries\n");
    fprintf (stderr, " -n     : Nosanitize: leaved undetected entries untouched\n");
    fprintf (stderr, " -d     : sanitize by Deleting undetected entries (def: .shadow. files\n");
    fprintf (stderr, " -l/-L  : create symLinks for device names / alias names\n");
    fprintf (stderr, " -m mode: permissions to create dev nodes with\n");
    fprintf (stderr, " -s     : list Serial numbers /WWIDs /HSVs of devices (if available)\n");
    fprintf (stderr, " -c mxms: Continue scanning until mxms missing devs found\n");
    fprintf (stderr, " -A file: alias file (default: /etc/scsi.alias)\n");
    fprintf (stderr, " -r     : trust Removeable media (only safe after boot)\n");
    fprintf (stderr, " -e     : use dEvfs like naming  (cbtu chars)\n");
    fprintf (stderr, " -o     : for the Old names use scd instead of sr\n");
    fprintf (stderr, " -M     : support Multipathing: First device is aliased\n");
    fprintf (stderr, " -v/-q  : Verbose/Quiet operation\n");
    fprintf (stderr, " -h     : print Help and exit.\n");
}

int main (int argc, char * argv[])
{
    int c;
    int show_serial = 0;
    struct stat statbuf;
    sname * spnt;
    int status;

    status = stat(DEVSCSI, &statbuf);
    if ( status == -1 )
	mkdir (DEVSCSI, 0755);
    status = stat(DEVSCSI, &statbuf);
    if ( status == -1 || !S_ISDIR(statbuf.st_mode)) {
	fprintf(stderr, DEVSCSI " either does not exist, or is not a directory\n");
	exit(0);
    }
    while ((c = getopt(argc, argv, "ypflLvqshnderoMm:c:A:")) != -1) {
	switch (c) {
	  case 'y':	/* undocumented */
	    no_sysfs = 1; break;
	  case 'p':	/* undocumented */
	    no_procscsi = 1; break;
	  case 'f':
	    force = 1; break;
	  case 'm':
	    filemode = strtoul (optarg, 0, 0); break;
	  case 'c':
	    maxmiss = strtoul (optarg, 0, 0); break;
	  case 'A':
	    scsialias = optarg; break;
	  case 'l':
	    use_symlink = 1; break;
	  case 'L':
	    symlink_alias = 1; break;
	  case 's':
	    show_serial = 1; break;
	  case 'n':
	    no_san = 1; break;
	  case 'd':
	    san_del = 1; break;
	  case 'r':
	    supp_rmvbl = 1; break;
	  case 'M':
	    supp_multi = 1; break;
	  case 'e':
	    nm_cbtu = 1; break;
	  case 'o':
	    use_scd = 1; break;  
	  case 'v':
	    verbose++; break;
	  case 'h':
	    fprintf (stderr, "%s\n%s\n", rcsid, copyright); 
	    usage (); exit (0); break;
	  case 'q':
	    quiet = 1; break;
	  default:
	    usage(); break;
	}
    }

    if( verbose >= 1 ) 
	fprintf( stderr, "%s\n", versid );
    
    /* Now, we need to make sure all high-level modules are loaded */
    trigger_module_loads ();

    if( force ) 
	flush_sdev ();

#ifdef DEBUG
    register_dev("/dev/scsi/sdh4-334c0i0l0",  8,  0, SD, 6, 0x334, 0, 0, 0, -1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sdh4-334c0i0l0p1",8,  1, SD, 6, 0x334, 0, 0, 0,  1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sdh4-334c0i0l0p2",8,  2, SD, 6, 0x334, 0, 0, 0,  2, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sdh4-334c0i0l0p3",8,  3, SD, 6, 0x334, 0, 0, 0,  3, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sgh4-334c0i0l0", 21,  0, SG, 6, 0x334, 0, 0, 0, -1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sgh4-334c0i2l0", 21,  1, SG, 6, 0x334, 0, 2, 0, -1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sgh4-334c0i5l0", 21,  2, SG, 6, 0x334, 0, 5, 0, -1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/srh4-334c0i2l0", 11,  0, SR, 6, 0x334, 0, 2, 0, -1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/sth4-334c0i5l0",  9,  0, ST, 6, 0x334, 0, 5, 0, -1, "debug", 0, NULL, NULL);
    register_dev("/dev/scsi/rsth4-334c0i5l0", 9,128, ST, 6, 0x334, 0, 5, 0, -1, "debug", 0, NULL, NULL);
#else
    if (no_procscsi || try_procscsi ()) {
	if (no_sysfs || find_sysfs ()) {
	    if (!quiet) 
		fprintf (stderr, "/proc/scsi/scsi extensions not found. Fall back to scanning.\n");
	    build_sgdevlist ();
	}
    }
#endif

    if( show_serial ) {
	if (verbose)
	    dumplist();
	for (spnt = reglist; spnt; spnt = spnt->next) {
	    if( spnt->partition != -1 ) 
		continue;
	    if( (spnt->devtp == ST || spnt->devtp == OSST)
		&& (spnt->minor & 0x80) != 0 )
		continue;

	    //if( spnt->serial == NULL ) inquiry (spnt);
	    if( spnt->serial == no_serial )
		printf("Device  %s has no serial number\n", spnt->name);
	    else
		printf("Serial number of %s: \"%s\"\n", spnt->name, spnt->serial);
	    if (!spnt->name)
		    dumpentry(spnt);
	    if ( spnt->wwid != no_wwid )
		printf (" WWID: %Lx\n", spnt->wwid);
	    if ( spnt->hsv_os_id != no_hsv_os_id )
		printf (" HSV OS Id: %d\n", spnt->hsv_os_id);
	}
    }


    //dumplist ();
    /*
     * Now, read the configuration file and see whether there
     * are any special device names we want to try and match.
     */
    build_special ();

    /* flush_sdev () has been changed to delete all, so the if is correct */
    if (!force)
	sanitize_sdev ();

    return 0;
}

char * get_string (char * pnt, char **result)
{
    char quote = 0;

    while (*pnt == ' ' || *pnt == '\t') pnt++;

    if( *pnt == '"' || *pnt == '\'') 
	quote = *pnt++;

    *result = pnt;

    if( quote != 0 ) {
	while ( *pnt != quote ) pnt++;
	*pnt++ = 0;
    } else {
	while ( *pnt != ',' && *pnt != ' ' && *pnt != '\t' && *pnt != '\0' ) 
	    pnt++;
	*pnt++ = 0;
    }

    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    if (*pnt == ',') 
	pnt++;
    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    return pnt;
}

char * get_llnumber (char * pnt, unsigned long long * result)
{
    int base = 10;
    unsigned long long num;

    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    if (pnt[0] == '0' && pnt[1] == 'x') { 
	base = 16; pnt += 2;
    }

    num = 0;
    while (1) {
	if (base == 10 && *pnt >= '0' && *pnt <= '9' ) {
	    num = num * 10ULL + *pnt - '0';
	    pnt++;
	    continue;
	}
	else if ( base == 16 ) {
	    if (*pnt >= '0' && *pnt <= '9') {
		num = (num << 4) + *pnt - '0';
		pnt++;
		continue;
	    }
	    if (*pnt >= 'a' && *pnt <= 'f') {
		num = (num << 4) + *pnt - 'a' + 10;
		pnt++;
		continue;
	    }
	    if (*pnt >= 'A' && *pnt <= 'F') {
		num = (num << 4) + *pnt - 'A' + 10;
		pnt++;
		continue;
	    }
	    break;
	}
	/*
	 * Isn't a digit.  Must be the end of the number.
	 */
	break;
    }
    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    if (*pnt == ',') 
	pnt++;
    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    *result = num;
    return pnt;

}

char * get_number (char * pnt, int * result)
{
    int base = 10;
    int num;

    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    if (pnt[0] == '0' && pnt[1] == 'x') { 
	base = 16; pnt += 2; 
    }

    num = 0;
    while (1) {
	if (base == 10 && *pnt >= '0' && *pnt <= '9' ) {
	    num = num * 10 + *pnt - '0';
	    pnt++;
	    continue;
	}
	else if ( base == 16 ) {
	    if (*pnt >= '0' && *pnt <= '9') {
		num = (num << 4) + *pnt - '0';
		pnt++;
		continue;
	    }
	    if (*pnt >= 'a' && *pnt <= 'f') {
		num = (num << 4) + *pnt - 'a' + 10;
		pnt++;
		continue;
	    }
	    if (*pnt >= 'A' && *pnt <= 'F') {
		num = (num << 4) + *pnt - 'A' + 10;
		pnt++;
		continue;
	    }
	    break;
	}
	/*
	 * Isn't a digit.  Must be the end of the number.
	 */
	break;
    }
    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    if (*pnt == ',') 
	pnt++;
    while (*pnt == ' ' || *pnt == '\t') 
	pnt++;
    *result = num;
    return pnt;

}

/*
 * The configuration file is designed to be something that can match
 * any number of fields.  Thus we need to be able to specify a large
 * number of different things in the hope that we can uniquely match
 * to one specific device.
 *
 * Each match contains a series of tokens:
 *
 * ID=number
 * LUN=number
 * CHANNEL=number
 * HOSTID=number
 * HOST="string" (hostname)
 * MANUFACTURER="string"
 * MODEL="string"
 * SERIAL_NUMBER="string"	(for those devices that support this).
 * WWID=number			( "    "      "     "      "      " )
 * HSVOSID=number		( "    "      "     "      "      " )
 * REV="string"
 * NAME="string" (alias)
 * DEVTYPE="disk", "tape", "osst", "generic", or "cdrom".
 */
	
void build_special ()
{
    FILE *	configfile;
    char buffer[256];
    char * pnt;
    char * pnt1;
    sname * spnt, * spnt1, *match;
    char scsidev[64];

    int lun, chan, id, part, hostid, hostnum;
    int line;
    int hsv_os_id;
    unsigned long long wwid;	/* host byte order ... */
    enum devtype_t devtype_i;
    char *manufacturer, *model, *serial_number, *name, *devtype, *rev, *host;

    if (!*scsialias) {
#ifdef DEBUG
      scsialias = "scsi.alias";
#else
      scsialias = "/etc/scsi.alias";
#endif
    }

    configfile = fopen (scsialias, "r");
    if (!configfile) {
	if (verbose) perror (scsialias);
	return;
    }

    line = 0;
    while (1) {
	*buffer = 0;
	fgets (buffer, sizeof(buffer), configfile);
	line++;
	if (feof (configfile) && !*buffer) 
	    break;
	
	/*
	 * Remove trailing \n, if present.
	 */
	pnt = buffer + strlen(buffer) - 1;
	if( *pnt == '\n' ) 
	    *pnt = '\0';

	/*
	 * First, tokenize the input line, and pick out the parameters.
	 */
	lun = -1; id = -1;
	chan = -1;
	hostid = -1; hostnum = -1;
	part = -1; wwid = no_wwid;
	hsv_os_id = -1;
	host = NULL;
	manufacturer = NULL; model = NULL;
	serial_number = NULL; rev = NULL;
	name = NULL; devtype_i = NONE;
	devtype = NULL;
	pnt = buffer;
	while (*pnt == ' ' || *pnt == '\t') pnt++;

	/* allow blank lines and comments... */
	if( *pnt == '\0' ) 
	    continue;
	if( *pnt == '#'  ) 
	    continue;

	while (1) {
	    pnt1 = pnt;
	    while (*pnt1 != '=' && *pnt1 != '\0') 
		pnt1++;
	    if( *pnt1 == '\0' ) 
		break;

	    *pnt1 = '\0';
	    if( strncmp(pnt, "manu", 4) == 0 )
		pnt = get_string(pnt1 + 1, &manufacturer);
	    else if ( strncmp(pnt, "mode", 4) == 0 )
		pnt = get_string(pnt1 + 1, &model);
	    else if ( strncmp(pnt, "seri", 4) == 0 )
		pnt = get_string(pnt1 + 1, &serial_number);
	    else if ( strcmp(pnt, "wwid") == 0 )
		pnt = get_llnumber(pnt1 + 1, &wwid);
	    else if ( strncmp(pnt, "rev", 3) == 0 )
		pnt = get_string(pnt1 + 1, &rev);
	    else if ( strncmp(pnt, "hostname", 6) == 0 )
		pnt = get_string(pnt1 + 1, &host);
	    else if ( strcmp(pnt, "id") == 0 )
		pnt = get_number(pnt1 + 1, &id);
	    else if ( strcmp(pnt, "lun") == 0 )
		pnt = get_number(pnt1 + 1, &lun);
	    else if ( strncmp(pnt, "chan", 4) == 0 )
		pnt = get_number(pnt1 + 1, &chan);
	    else if ( strncmp(pnt, "part", 4) == 0 )
		pnt = get_number(pnt1 + 1, &part);
	    else if ( strcmp(pnt, "hostid") == 0 )
		pnt = get_number(pnt1 + 1, &hostid);
	    else if ( strcmp(pnt, "hostnum") == 0 )
		pnt = get_number(pnt1 + 1, &hostnum);
	    else if ( strncmp(pnt, "alia", 4) == 0 )
		pnt = get_string(pnt1 + 1, &name);
	    else if ( strncmp(pnt, "devt", 4) == 0 )
		pnt = get_string(pnt1 + 1, &devtype);
	    else if ( strcmp(pnt, "hsvosid") == 0 )
		pnt = get_number(pnt1 + 1, &hsv_os_id);
	    else {
		fprintf(stderr,"Unrecognized specifier \"%s\" on line %i\n", pnt,
			line);
		break;
	    }
	}

	/*
	 * OK, got one complete entry.  Make sure it has the required
	 * fields, and then attempt to match it to a real device.
	 */
	if( name == NULL ) {
	    fprintf(stderr,"Line %d is missing \"alias\" specifier\n", line);
	    continue;
	}
	if( devtype == NULL ) {
	    fprintf(stderr,"Line %d is missing \"devtype\" specifier\n", line);
	    continue;
	}
	if( strcmp(devtype, "disk") == 0 )
	    devtype_i = SD;
	else if( strcmp(devtype, "cdrom") == 0)
	    devtype_i = SR;
	else if( strcmp(devtype, "tape") == 0)
	    devtype_i = ST;
	else if( strcmp(devtype, "osst") == 0)
	    devtype_i = OSST;
	else if(strcmp(devtype, "generic") == 0 )
	    devtype_i = SG;
	else if(strcmp(devtype, "changer") == 0 )
	    devtype_i = SCH;
	else {
	    fprintf(stderr,"Line %d has invalid  \"devtype\" specifier(%s)\n", 
		    line, devtype);
	    continue;
	}

	/*
	 * OK, minimal requirements are met.  Try and match this to something
	 * we know about already.
	 */
	match = NULL;
	for (spnt = reglist; spnt; spnt = spnt->next) {
	    /* Don't alias aliases */
	    if( spnt->alias != NULL )
		continue;
	    /*
	     * Check the integers first.  Some of the strings we have to
	     * request, and we want to avoid this if possible.
	     */
	    if( id != -1 && id != spnt->id ) 
		continue;
	    if( chan != -1 && chan != spnt->chan )
		continue;
	    if( lun != -1 && lun != spnt->lun ) 
		continue;
	    if( hostid != -1 && hostid != spnt->hostid ) 
		continue;
	    if( hostnum != -1 && hostnum != spnt->hostnum ) 
		continue;
	    if( hsv_os_id != -1 && hsv_os_id != spnt->hsv_os_id ) 
		continue;
	    if( spnt->devtp != devtype_i )
		continue;
	    if( part != spnt->partition )
		continue;
	    if( (spnt->devtp == ST || spnt->devtp == OSST)
		&& (spnt->minor & 0x80) != 0) 
		continue;
	    if( wwid != no_wwid && wwid != spnt->wwid ) 
		continue;

	    /*
	     * OK, that matches, now obtain some of the strings
	     * that might be needed.
	     */
	    if( manufacturer != NULL && (spnt->manufacturer == NULL ||
					 strcmp(spnt->manufacturer, manufacturer) != 0 ))
		continue;

	    if( model != NULL && (spnt->model == NULL ||
				  strcmp(spnt->model, model) != 0 ))
		continue;

	    if( serial_number != NULL && (spnt->serial == NULL ||
					  strcmp(spnt->serial, serial_number) != 0 ))
		continue;

	    if( rev != NULL && (spnt->rev == NULL ||
				strcmp(spnt->rev, rev) != 0 ))
		continue;

	    if( host != NULL 
		&& (spnt->hostname == NULL ||
				 strncmp(spnt->hostname, host, strlen(host)) != 0)
		&& (spnt->shorthostname == NULL ||
		    strncmp(spnt->shorthostname, host, strlen(host)) != 0) )
			continue;

	    /*
	     * We have a match.  Record it and keep looking just in
	     * case we find a duplicate.
	     */
	    if( match != NULL ) {
		if (!supp_multi) {
		    fprintf (stderr, "Line %d not matched uniquely\n", line);
		    fprintf (stderr, " Prev. match: %s\n", match->name);
		    fprintf (stderr, " Curr. match: %s\n", spnt->name);
		    break;
		} else {
		    if (!quiet) 
			fprintf (stderr, "Line %d: %s <=> %s\n",
				 line, match->name, spnt->name);
		}
	    } else
		match = spnt;
	}

	/*
	 * See if there was a non-unique mapping.  If so, then
	 * don't do anything for this one.
	 */
	    
	// detect break
	if( spnt != NULL )
	    continue;

	if( match != NULL ) {
	    /*
	     * OK, we have a unique match.  Create the device entries,
	     * as requested.
	     */
	    if (!quiet) {
		fprintf (stderr, "Alias device %s: %s (%s)", name,
			 strrchr (match->name, '/') + 1,
			 match->oldname);
		if (match->related)
		    fprintf (stderr, " -> (%s, %s)\n",
			     strrchr (match->related->name, '/') + 1,
			     match->related->oldname);
		else 
		    fprintf (stderr, "\n");
	    }

	    /*
	     * If this is just an ordinary single device type,
	     * Just create it.
	     */
	    sprintf (scsidev, DEVSCSI "/%s", name);
	    spnt1 = register_dev (scsidev, match->major, match->minor,
				  match->devtp, match->hostnum, match->hostid,
				  match->chan, match->id, match->lun, 0,
				  match->hostname, match->name, match, 0);
	    create_dev (spnt1, symlink_alias);

	    if( devtype_i == ST || devtype_i == OSST ) {
		char nm2[64]; char * ptr; 
		ptr = strrchr (match->name, '/');
		strcpy (nm2, "scsi/n");
		strcat (nm2, ptr? ptr+1: match->name);
		sprintf (scsidev, DEVSCSI "/n%s", name);

		spnt1 = register_dev (scsidev, match->major, match->minor | 0x80,
				      match->devtp, match->hostnum, match->hostid,
				      match->chan, match->id, match->lun, 0,
				      match->hostname, nm2, match, spnt1);
		create_dev (spnt1, symlink_alias);
	    }

	    if ( devtype_i == SD 
		 && match->partition == -1 ) {
		/*
		 * This is the master entry for a disk.
		 * we need to go through and generate entries
		 * for each partition.  The trick is to find
		 * all of the related entries so we know which
		 * ones we actually need to create.
		 */
		for( spnt = reglist; spnt; spnt = spnt->next ) {
		    sname * spnt2;
		    if( spnt->alias != NULL ) continue;
		    if( spnt->partition == -1 ) continue;
		    if( spnt->devtp != devtype_i ) continue;
		    if( spnt->id != match->id ) continue;
		    if( spnt->lun != match->lun ) continue;
		    if( spnt->chan != match->chan ) continue;
		    if( spnt->hostnum != match->hostnum ) continue;
		    if( spnt->hostid != match->hostid ) continue;

		    sprintf(scsidev, DEVSCSI "/%s-p%d", name, 
			    spnt->partition);
		    spnt2 = register_dev (scsidev, match->major, spnt->minor,
					  match->devtp, match->hostnum, match->hostid,
					  match->chan, match->id, match->lun, spnt->partition,
					  match->hostname, spnt->name, spnt, spnt1);
		    create_dev (spnt2, symlink_alias);
		}
	    }
	} else {
	    if (!quiet) 
		fprintf (stderr, "Unable to match device for line %d (alias %s)\n", 
			 line, name);
	}
    }

    fclose (configfile);
}

/****************************** INQUIRY ***************************/

void dumppage (unsigned char* page)
{
    int ln = 4 + page[3];
    int i;
    for (i = 0; i < ln; i++)
    {
	printf (" %02x", page[i]);
	if (!((i+1)%16)) printf ("\n");
    }
    if (i%16) printf ("\n");
}


void dumppage_83 (unsigned char* page)
{
    int ln = 4 + (page[2] << 8) + page[3];
    int i;
    for (i = 0; i < ln; i++)
    {
	printf (" %02x", page[i]);
	if (!((i+1)%16)) printf ("\n");
    }
    if (i%16) printf ("\n");
}


char* getstr (char* page, int start, int stop)
{
	int ln;
	char* str;
	/* Remove leading spaces */
	while (*(page+start) == ' ' && start < stop)
		++start;
	/* Remove trailing spaces */
	while (*(page+stop) == ' ' && stop > start)
		--stop;
	/* empty */
	if (stop == start)
		return 0;
	/* otherwise copy */
	ln = stop-start+1;
	str = (char*) malloc (ln+1);
	memcpy (str, page+start, ln);
	str[ln] = 0;
	return str;
}

struct pg83id {
	unsigned char pident;
	unsigned char idtype;
	unsigned char res;
	unsigned char idlen;
	unsigned char iddata[8];
};

struct pg83 {
	unsigned char periph;
	unsigned char pgcode;
	unsigned short length;	/* big endian ! */
	struct pg83id idlist;
};
	
unsigned long long get_no(unsigned char* data, 
		          unsigned char start, unsigned char stop)
{
	unsigned int dat = ntohl(*(unsigned int*) data);
	/* Clear left bits if number does not start at 0 */
	dat  &= (0xffffffff >> start);
	/* Shift right if stop is not 32bits away */
	dat >>= (32-stop);
	return dat;
}


/* Return the wwid as 64bit number, high 32bits have vendor ID (IEEE)
 * and low have device ID */
unsigned long long extract_wwid (unsigned char* page)
{
	struct pg83 *p83 = (struct pg83*) page;
	struct pg83id *pid = &p83->idlist;
	unsigned int len = ntohs(p83->length);
	
	if (p83->pgcode != 0x83) {
	    printf("Page does not contain any WWID\n");
	    return no_wwid;
	}

	if (pid->res != 0) {
		/* Pre SCSI-2 / pre-SPC answer */
		return get_no(&pid->pident  , 0, 32) << 32
		     | get_no(&pid->pident+4, 0, 32);
	}
	
	for (;
	     (char*)pid < (char*)p83 + 4 + len;
	     pid = (struct pg83id*) ((char*)pid + 4 + pid->idlen)) {
		/* SKip over per target of per port association */
		unsigned char assoc  = (pid->idtype & 0x30) >> 4;
		unsigned char code   =  pid->pident & 0x0f;
		unsigned char idtype =  pid->idtype & 0x0f;
		if (assoc != 0)
			continue;
		/* EUI-64, should always be binary, */
		if (idtype == 2 && code  == 1) {
			if (pid->idlen == 8 || pid->idlen == 12 
					    || idtype == 3)
				return get_no(pid->iddata  , 0, 32) << 32 
				     | get_no(pid->iddata+4, 0, 32);
			else if (pid->idlen == 16)
				return get_no(pid->iddata+4, 0, 32) << 32
				     | get_no(pid->iddata+8, 0, 32);
			else continue;
		}
		/* NAA */
		if (idtype == 3 && code == 1) {
			unsigned char naa = (pid->iddata[0] & 0xf0) >> 4;
			if (naa == 2) 
				return  get_no(pid->iddata+2, 0, 24) << 32
				     | (get_no(pid->iddata  , 4, 12) & 0xff) << 24
				     |  get_no(pid->iddata+5, 0, 24);
			else if (naa == 5 || naa == 6)
				return get_no(pid->iddata  , 4, 28) << 36
				     | get_no(pid->iddata+3, 4,  8) << 32
				     | get_no(pid->iddata+4, 0, 32);
			else 
				continue;
		}
		/* We can't really handle T10, it's ASCII/UTF8 */
		if (idtype == 1 && code == 2 && verbose) {
			char  ven_id[10], dev_id[130];
			memcpy(ven_id, pid->iddata, 8);
			ven_id[9] = 0;
			memcpy(dev_id, pid->iddata+8, pid->idlen-8);
			dev_id[pid->idlen] = 0;
			printf("T10 ID: \"%s\" \"%s\"\n", ven_id, dev_id);
			continue;
		}
	}
	return no_wwid;
}

#ifndef SG_IO
void my_memmove(unsigned char* dst, unsigned char* src, unsigned int ln)
{
	if (src > dst) {
		while (ln--)
			*dst++ = *src++;
	} else {
		dst += ln; src += ln;
		while (ln--)
			*(--dst) = *(--src);
	}
}
#endif

int scsi_cmd(int file, int rlen,
	     unsigned char* cmd, int cmdlen, 
	     unsigned char* buf, int buflen,
	     unsigned char* sen, int senlen)
{
	int ret;
#ifdef SG_IO
	sg_io_hdr_t sghdr;
	memset(&sghdr, 0, sizeof(sg_io_hdr_t));
	sghdr.interface_id = 'S';
	sghdr.dxfer_direction = SG_DXFER_FROM_DEV;
	sghdr.cmd_len = cmdlen;
	sghdr.iovec_count = 0;
	sghdr.dxfer_len = rlen;
	sghdr.dxferp = buf;
	sghdr.cmdp = cmd;
	sghdr.mx_sb_len = senlen;
	sghdr.sbp = sen;
	sghdr.timeout = 2000;
	if (sen)
		memset(sen, 0, senlen);
	memset(buf, 0, buflen);

	ret = ioctl(file, SG_IO, &sghdr);
	if (verbose >= 2)
		printf("SG_IO %02x %02x %02x: ret=%i, status=%i (host %i, drv %i), read=%i/%i\n",
		       cmd[0], cmd[1], cmd[2],	
		       ret, sghdr.status, sghdr.host_status, sghdr.driver_status,
		       rlen-sghdr.resid, rlen);
	return ret + sghdr.status;
#else
	memset(buf, 0, buflen);
	*(  (int *) buf)     = 0;	/* Length of input data */
	*( ((int *) buf+1) ) = rlen;	/* Length of output data */
	memcpy(buf+8, cmd, cmdlen);
	ret = ioctl(file, SCSI_IOCTL_SEND_COMMAND, buf);
	my_memmove(buf, buf+8, buflen-8);
	return ret;
#endif
}

#define INQBUFSZ 512
int get_inq_page (int file, int lun, unsigned char* buf, unsigned char page, char evpd)
{
	unsigned char cmd[6] = { 0x12, (lun << 5 ) | (evpd? 1: 0), page,
				 0x00, 0xfc, 0x00 };
	return scsi_cmd(file, 0xfc, cmd, 6, buf, INQBUFSZ, NULL, 0);
}
	
int inquiry (int infile, sname * spnt)
{
#ifdef DEBUG
    /*
     * Fill in some entries just so that I can test this.
     */
    if(spnt->id == 0 ) {
	spnt->manufacturer = strdup("CONNER");
	spnt->model=strdup("CFP4207S");
    } else if(spnt->id == 2 ) {
	spnt->manufacturer = strdup("HP");
	spnt->model=strdup("C4324/C4325");
    } else if(spnt->id == 5 ) {
	spnt->manufacturer = strdup("WANGTEK");
	spnt->model=strdup("5150ES");
    }
#else
    int status;
    unsigned char buffer[INQBUFSZ];
    unsigned char * const pagestart = buffer;// + 8;
    //int infile;
    char have_ser_page = 0;
    char have_wwid_page = 0;
    int ln; int off;
    int lun; int ansi;
	
    spnt->wwid = no_wwid; spnt->serial = no_serial;
    //infile = open(spnt->name, O_RDWR);
    if (infile == -1) {
	fprintf(stderr,"No input file for inquiry!\n");
	return -1;
    }

    // Std. inquiry
    status = get_inq_page (infile, 0, buffer, 0, 0);

    if (status) { 
	fprintf (stderr, "INQUIRY failed for %s (%i-%i/%03x:%05x)!\n",
		 spnt->name, spnt->id, spnt->lun, spnt->major, spnt->minor);
	return -1;
    }
    /* dumppage does not make sense for std INQUIRY */

    spnt->manufacturer = getstr (pagestart, 8, 15); 
    spnt->model = getstr (pagestart, 16, 31);
    spnt->rev = getstr (pagestart, 32, 35);
    spnt->inq_devtp = pagestart[0] & 0x1f;
    if (verbose >= 2)
	printf("Device type: %X\n",spnt->inq_devtp);
    spnt->rmvbl = (pagestart[1] & 0x80) >> 7;
    if (verbose >= 2)
	printf("Device removable: %s\n",spnt->rmvbl?"yes":"no");
    ansi = pagestart[2] & 7;
    if (verbose >= 2)
	printf("ANSI SCSI version: %X\n", ansi);
    if (verbose >= 2)
	printf("Desc1: %X\n",pagestart[58]);

    if (ansi >= 3)
	lun = 0;
    else
	lun = spnt->lun;

    /* TODO: Extract serial number from bytes 36--43 ? */
    
    // List of supported EVPD pages ...
    if (get_inq_page (infile, lun, buffer, 0, 1))
	return 0;
    ln = pagestart[3];
    for (off = 0; off < ln; ++off) {
	if (verbose >= 2)    
	    printf("Supported VPD page: %x\n", pagestart[4+off]);
	if (pagestart[4+off] == 0x80)
	    have_ser_page = 1;    
	if (pagestart[4+off] == 0x83)
	    have_wwid_page = 1;    
    }
    
    if (have_ser_page && !get_inq_page (infile, lun, buffer, 0x80, 1)) {
	if (verbose >= 2) {    
	    printf("VPD Page 0x80\n");
	    dumppage(pagestart);
	}
	spnt->serial = getstr (pagestart, 4, 3+pagestart[3]);
	if (verbose >= 2) 
	    printf ("Serial for %s: %s\n", spnt->name, spnt->serial);
    }

    if (have_wwid_page && !get_inq_page (infile, lun, buffer, 0x83, 1)) {
	if (verbose >= 2) {
	    printf("VPD Page 0x83\n");
	    dumppage_83(pagestart);
	}
	spnt->wwid = extract_wwid (pagestart);

	if (verbose >= 2)
	    printf ("WWID for %s: %Lx\n", spnt->name, spnt->wwid);
    }

    //close(infile);
    return 0;
#endif
}

int get_hsv_os_id (int infile, sname * spnt)
{
  int status,i;
  unsigned char buffer[1024];
  unsigned char *pagestart = buffer;
  char path[64];
  
  unsigned char cmd[12] = {
	  0xa3, 0x05, 0x00 /*res*/, 0x00 /*res*/,
	  0x00 /* lun ign */, 0x00 /* lun ign */,
	  0x00 /* len */, 0x00 /* len */, 0x00 /* len */, 0xfc /* len */,
	  0x00, 0x00 };
  
  spnt->hsv_os_id = no_hsv_os_id;

  if (!spnt->model || strncmp (spnt->model, "HSV", 3) != 0)
       return -1;
  if( infile == -1 ) 
	return -1;
  
  status = scsi_cmd(infile, 0xfc, cmd, 12, buffer, 1024, NULL, 0);

  if (status) 
	spnt->hsv_os_id = no_hsv_os_id;
  else
	spnt->hsv_os_id = (pagestart[4])<<8 | (pagestart[5]);

  if (verbose == 1) 
	printf ("HSV OS Unit ID for %s: %d\n", path, spnt->hsv_os_id);

  if (verbose == 2) {
	for (i = 0; i < 16; i++) {
		printf (" %02x", pagestart[i]);
		if (!((i+1)%16)) 
			printf ("\n");
	}
	printf("\n");
  }
  return 0;
}

