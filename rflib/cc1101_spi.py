#!/usr/bin/env ipython

from __future__ import print_function
from __future__ import absolute_import
from __future__ import division

from builtins import bytes
from builtins import str
from builtins import hex
from builtins import range
from builtins import object
from past.utils import old_div
from datetime import datetime
import os
import sys
import usb
import time
import struct
import select
import threading
import wiringpi
from binascii import hexlify

from . import bits
from .cc1101defs import *
from .rflib_defs import *
from .rflib_version import *
from .bits import correctbytes

if os.name == 'nt':
    import msvcrt

DEFAULT_SPI_TIMEOUT = 1000

EP_TIMEOUT_IDLE     = 400
EP_TIMEOUT_ACTIVE   = 10

SPI_MAX_BLOCK_SIZE  = 512
SPI_RX_WAIT         = 1000
SPI_TX_WAIT         = 10000

USB_MAX_BLOCK_SIZE  = 512
USB_RX_WAIT         = 1000
USB_TX_WAIT         = 10000

APP_GENERIC                     = 0x01
APP_DEBUG                       = 0xfe
APP_SYSTEM                      = 0xff

SYS_CMD_PEEK                    = 0x80
SYS_CMD_POKE                    = 0x81
SYS_CMD_PING                    = 0x82
SYS_CMD_STATUS                  = 0x83
SYS_CMD_POKE_REG                = 0x84
SYS_CMD_GET_CLOCK               = 0x85
SYS_CMD_BUILDTYPE               = 0x86
SYS_CMD_BOOTLOADER              = 0x87
SYS_CMD_RFMODE                  = 0x88
SYS_CMD_COMPILER                = 0x89
SYS_CMD_VERSION                 = 0x8d
SYS_CMD_PARTNUM                 = 0x8e
SYS_CMD_RESET                   = 0x8f
SYS_CMD_CLEAR_CODES             = 0x90
SYS_CMD_LED_MODE                = 0x93

EP0_CMD_GET_DEBUG_CODES         = 0x00
EP0_CMD_GET_ADDRESS             = 0x01
EP0_CMD_POKEX                   = 0x01
EP0_CMD_PEEKX                   = 0x02
EP0_CMD_PING0                   = 0x03
EP0_CMD_PING1                   = 0x04
EP0_CMD_RESET                   = 0xfe


DEBUG_CMD_STRING                = 0xf0
DEBUG_CMD_HEX                   = 0xf1
DEBUG_CMD_HEX16                 = 0xf2
DEBUG_CMD_HEX32                 = 0xf3
DEBUG_CMD_INT                   = 0xf4

EP5OUT_MAX_PACKET_SIZE          = 64
EP5IN_MAX_PACKET_SIZE           = 64
# EP5OUT_BUFFER_SIZE must match firmware/include/chipcon_usb.h definition
EP5OUT_BUFFER_SIZE              = 516

LC_USB_INITUSB                = 0x2
LC_MAIN_RFIF                  = 0xd
LC_USB_DATA_RESET_RESUME      = 0xa
LC_USB_RESET                  = 0xb
LC_USB_EP5OUT                 = 0xc
LC_RF_VECTOR                  = 0x10
LC_RFTXRX_VECTOR              = 0x11

LCE_USB_EP5_TX_WHILE_INBUF_WRITTEN    = 0x1
LCE_USB_EP0_SENT_STALL                = 0x4
LCE_USB_EP5_OUT_WHILE_OUTBUF_WRITTEN  = 0x5
LCE_USB_EP5_LEN_TOO_BIG               = 0x6
LCE_USB_EP5_GOT_CRAP                  = 0x7
LCE_USB_EP5_STALL                     = 0x8
LCE_USB_DATA_LEFTOVER_FLAGS           = 0x9
LCE_RF_RXOVF                          = 0x10
LCE_RF_TXUNF                          = 0x11

RCS = {}
LCS = {}
LCES = {}
lcls = locals()
for lcl in list(lcls.keys()):
    if lcl.startswith("LCE_"):
        LCES[lcl] = lcls[lcl]
        LCES[lcls[lcl]] = lcl
    if lcl.startswith("LC_"):
        LCS[lcl] = lcls[lcl]
        LCS[lcls[lcl]] = lcl
    if lcl.startswith("RC_"):
        RCS[lcl] = lcls[lcl]
        RCS[lcls[lcl]] = lcl

CHIPS = {
    0x91: "CC2511",
    0x81: "CC2510",
    0x11: "CC1111",
    0x01: "CC1110",
    0x00: "CC1101",
    }


def keystop(delay=0):
    if os.name == 'posix':
        return len(select.select([sys.stdin],[],[],delay)[0])
    else:
        return msvcrt.kbhit()

def getRfCatDevices():
    '''
    returns a list of SPI device objects for any rfcats that are plugged in
    '''
    rfcats = []
    rfcats.append(wiringpi) # RPi has 2 SPIs
    #rfcats.append(wiringpi) # RPi has 2 SPIs
    return rfcats

class ChipconUsbTimeoutException(Exception):
    def __str__(self):
        return "Timeout waiting for SPI response."

direct=False

class SPIDongle(object):
    ######## INITIALIZATION ########
    def __init__(self, idx=0, debug=False, copyDongle=None, RfMode=RFST_SRX):
        self.rsema = None
        self.xsema = None
        self._bootloader = False
        self._init_on_reconnect = True
        self._do = None
        self.idx = idx
        self.cleanup()
        self._debug = debug
        self._quiet = False
        self._threadGo = threading.Event()
        self._recv_time = 0
        self.radiocfg = RadioConfig()
        self._rfmode = RfMode
        self._radio_configured = False

        self.ctrl_thread = threading.Thread(target=self.run_ctrl)
        self.ctrl_thread.setDaemon(True)
        self.ctrl_thread.start()

        # XXX: We do not have RX/TX threads yet

        #self.recv_thread = threading.Thread(target=self.runEP5_recv)
        #self.recv_thread.setDaemon(True)
        #self.recv_thread.start()

        #self.send_thread = threading.Thread(target=self.runEP5_send)
        #self.send_thread.setDaemon(True)
        #self.send_thread.start()

        self.resetup(copyDongle=copyDongle)
        self.max_packet_size = SPI_MAX_BLOCK_SIZE

    def cleanup(self):
        self._usberrorcnt = 0;
        self.recv_queue = ''
        self.recv_mbox  = {}
        self.recv_event = threading.Event()
        self.xmit_event = threading.Event()
        self.reset_event = threading.Event()
        self.xmit_queue = []
        self.xmit_event.clear()
        self.reset_event.clear()
        self.trash = []
   
    def setRFparameters(self):
        pass

    def run_ctrl(self):
        '''
        we wait for reset events and run resetup
        '''
        while True:
            self.reset_event.wait()
            self.resetup(False)
            self.reset_event.clear()
            time.sleep(4)

    def setup(self, console=True, copyDongle=None):
        global dongles

        if copyDongle is not None:
            self.devnum = copyDongle.devnum
            self._d = copyDongle._d
            self._do = copyDongle._do
            self._usbmaxi = copyDongle._usbmaxi
            self._usbmaxo = copyDongle._usbmaxo
            self._usbcfg = copyDongle._usbcfg
            self._usbintf = copyDongle._usbintf
            self._usbeps = copyDongle._usbeps
            self._threadGo.set()
            self.ep5timeout = EP_TIMEOUT_ACTIVE
            copyDongle._threadGo.clear()            # we're taking over from here.
            self.rsema = copyDongle.rsema
            self.xsema = copyDongle.xsema
            return

        dongles = []
        self.ep5timeout = EP_TIMEOUT_ACTIVE

        devnum = 0
        for dev in getRfCatDevices():
            if self._debug: print((dev), file=sys.stderr)
            wiringpi.wiringPiSetup() 
            wiringpi.wiringPiSPISetup(devnum, 8000000)
            #do = dev.open() # SPI has no open() function
            #iSN = do.getDescriptor(1,0,50)[16]
            dongles.append((devnum, dev, wiringpi))
            devnum+=1

        dongles.sort()
        if len(dongles) == 0:
            raise Exception("No Dongle Found.  Please insert a RFCAT dongle.")

        self.rsema = threading.Lock()
        self.xsema = threading.Lock()

        # claim that interface!
        #do = dongles[self.idx][2]
        #
        #try:
        #    do.claimInterface(0)
        #except Exception as e:
        #    if console or self._debug: print(("Error claiming usb interface:" + repr(e)), file=sys.stderr)


        self.devnum, self._d, self._do = dongles[self.idx]
        self._usbmaxi, self._usbmaxo = (EP5IN_MAX_PACKET_SIZE, EP5OUT_MAX_PACKET_SIZE)
        self._usbcfg = 0 #self._d.configurations[0]
        self._usbintf = 0 # self._usbcfg.interfaces[0][0]
        self._usbeps = [] #self._usbintf.endpoints
        #for ep in self._usbeps:
        #    if ep.address & 0x80:
        #        self._usbmaxi = ep.maxPacketSize
        #    else:
        #        self._usbmaxo = ep.maxPacketSize

        self._threadGo.set()

        self.getRadioConfig()
        chip = self.getPartNum()
        chipstr = CHIPS.get(chip)

        self.chipnum = chip
        self.chipstr = chipstr

        if chip == None:
            print("Older firmware, consider upgrading.")
        else:
            self.chipstr = "unrecognized dongle: %s" % chip

        if self._init_on_reconnect:
            if self._radio_configured:
                self.setRadioConfig()
            else:
                self.setRFparameters()
                self._radio_configured = True

    def resetup(self, console=True, copyDongle=None):
        self._do=None
        if self._bootloader: 
            return
        if self._debug: print(("waiting (resetup) %x" % self.idx), file=sys.stderr)
        while (self._do==None):
            #try:
            print("resetup: setup")
            self.setup(console, copyDongle)
            print("resetup: copyDongle")
            print("resetup: ping")
            self.ping(3, wait=10, silent=True)
            print("resetup: setRfMode")
            self.setRfMode(self._rfmode)

            #except Exception as e:
            #    #if console: sys.stderr.write('.')
            #    if not self._quiet:
            #        print(("Error in resetup():" + repr(e)), file=sys.stderr)
            #    #if console or self._debug: print >>sys.stderr,("Error in resetup():" + repr(e))
            time.sleep(1)


    ########  BASE FOUNDATIONAL "HIDDEN" CALLS ########


    ######## APPLICATION API ########
    def recv(self, app, cmd=None, wait=SPI_RX_WAIT):
        '''
        high-level SPI receive.  
        checks the mbox for app "app" and command "cmd" and returns the next one in the queue
        if any of this does not exist yet, wait for a RECV event until "wait" times out.
        RECV events are generated by the low-level recv thread "runEP5_recv()"
        '''
        startTime = time.time()
        self.recv_event.clear() # an event is only interesting if we've already failed to find our message

        raise("someone tried to recv")

        while (time.time() - startTime)*1000 < wait:
            try:
                msg = bytes([0,0,0,0,0,0,0,0,0,0,0,0,0])
                retlen, retdata = self._d.wiringPiSPIDataRW(0, msg)
                print("SPI RX: {} bytes".format(retlen))
                return retdata, retlen
                #b = self.recv_mbox.get(app)
                #if b:
                #    if self._debug: print("Recv msg",app,b,cmd, file=sys.stderr)
                #    if cmd is None:
                #        keys = list(b.keys())
                #        if len(keys):
                #            cmd = list(b.keys())[-1] # just grab one.   no guarantees on the order

                #if b is not None and cmd is not None:
                #    q = b.get(cmd)
                #    if self._debug: print("debug(recv) q='%s'"%repr(q), file=sys.stderr)

                #    if q is not None and self.rsema.acquire(False):
                #        if self._debug>3: print(("rsema.UNlocked", "rsema.locked")[self.rsema.locked()],2)
                #        try:
                #            resp, rt = q.pop(0)

                #            self.rsema.release()
                #            if self._debug>3: print(("rsema.UNlocked", "rsema.locked")[self.rsema.locked()],2)

                #            # bring it on home...  this is the way out.
                #            return resp[4:], rt

                #        except IndexError:
                #            pass

                #        except AttributeError:
                #            sys.excepthook(*sys.exc_info())
                #            pass

                #        self.rsema.release()

                #self.recv_event.wait(old_div((wait - (time.time() - startTime)*1000),1000)) # wait on recv event, with timeout of remaining time
                #self.recv_event.clear() # clear event, if it's set

            except KeyboardInterrupt:
                sys.excepthook(*sys.exc_info())
                break
            except:
                sys.excepthook(*sys.exc_info())

        raise ChipconUsbTimeoutException

    def recvAll(self, app, cmd=None):
        retval = self.recv_mbox.get(app,None)
        if retval is not None:
            if cmd is not None:
                b = retval
                if self.rsema.acquire():
                    #if self._debug: print ("rsema.UNlocked", "rsema.locked")[self.rsema.locked()],3
                    try:
                        retval = b.get(cmd)
                        b[cmd]=[]
                        if len(retval):
                            retval = [ (d[4:],t) for d,t in retval ] 
                    except:
                        sys.excepthook(*sys.exc_info())
                    finally:
                        self.rsema.release()
                        #if self._debug: print ("rsema.UNlocked", "rsema.locked")[self.rsema.locked()],3
            else:
                if self.rsema.acquire():
                    #if self._debug: print ("rsema.UNlocked", "rsema.locked")[self.rsema.locked()],4
                    try:
                        self.recv_mbox[app]={}
                    finally:
                        self.rsema.release()
                        #if self._debug: print ("rsema.UNlocked", "rsema.locked")[self.rsema.locked()],4
            return retval

    def readreg(self, reg):
        msg = struct.pack("<B", reg + READ) + bytearray(1)
        retlen, retdata = self._d.wiringPiSPIDataRW(0, bytes(msg))
        if self._debug: print("RD - STATE: {:x} retlen {}" .format(bytes(retdata)[0], retlen))
        return int(retdata[1])

    def writereg(self, reg, val):
        msg = struct.pack("<BB", reg + WRITE, val)
        retlen, retdata = self._d.wiringPiSPIDataRW(0, bytes(msg))

    def readburst(self, reg, bytecount):
        msg = struct.pack("<B", reg + READ + BURST) + bytearray(bytecount)
        retlen, retdata = self._d.wiringPiSPIDataRW(0, bytes(msg))
        if self._debug: print("RB - STATE: {:x}" .format(bytes(retdata)[0]))
        return retdata[1:]

    def writeburst(self, reg, data):
        bytecount = len(data) - 1
        msg = struct.pack("<B", reg + WRITE + BURST) + bytearray(bytecount)
        retlen, retdata = self._d.wiringPiSPIDataRW(0, bytes(msg))
        if self._debug: print("RB - STATE: {:x}" .format(bytes(retdata)[0]))
        return retdata[1:]

    def send(self, app, cmd, buf, wait=SPI_TX_WAIT):
        if cmd == SYS_CMD_PEEK:
            bytecount, addr = struct.unpack("<HB", buf)
            if (bytecount > 1):
                addr += BURST + READ
            else:
                addr += READ
            msg = struct.pack("<B", addr) + bytearray(bytecount)
            if self._debug: print("PEEK {} b @ 0x{:x}".format(bytecount, addr))
            retlen, retdata = self._d.wiringPiSPIDataRW(0, bytes(msg))
            if self._debug: print("PEEK RX: 0x{}".format(hexlify(retdata[1:])))
            if self._debug: print("STATE: {:x}" .format(bytes(retdata)[0]))
            return retdata[1:], datetime.now()

        elif cmd == SYS_CMD_POKE:
            #r, t = self.send(APP_SYSTEM, SYS_CMD_POKE, struct.pack("<B", addr) + data)
            addr, = struct.unpack("<B", buf[0])
            if (len(buf) > 1):
                data = buf[1:]
                print("Got poke: 0x{}".format(hexlify(buf)))
                return self.writeburst(addr, data)
            else:
                self.writereg(addr + WRITE, 0x00) # STROBE
            if self._debug: print("cmd: POKE @ 0x{:x}     buf: {}".format(addr, buf.encode("hex")))
            return None, datetime.now()

        elif cmd == SYS_CMD_POKE_REG:
            #r, t = self.send(APP_SYSTEM, SYS_CMD_POKE_REG, struct.pack("<B", addr) + data)
            addr, = struct.unpack("<B", buf)
            if self._debug: print("cmd: POKE_REG @ 0x{:x} buf: {}".format(addr, buf.encode("hex")))
            raise("Not implemented yet")

        elif cmd == SYS_CMD_PARTNUM:
            partnum = self.readburst(PARTNUM, 1)
            print("PARTNUM: 0x{:x}" .format(bytes(partnum)[0]))
            return partnum, datetime.now()

        elif cmd == SYS_CMD_VERSION:
            version = self.readburst(VERSION, 1)
            print("VERSION: 0x{:x}" .format(bytes(version)[0]))
            return version, datetime.now()

        elif cmd == SYS_CMD_RFMODE:
            rfmode, = struct.unpack("<B", buf)
            if self._debug: print("RFMODE {}".format(rfmode))

            if rfmode == RFST_SRX:
                #// enter RX mode    (this is significant!  don't do lightly or quickly!)
                #void RxMode(void)
                #{
                #    if (rf_status != RFST_SRX)
                #    {
                #        MCSM1 &= 0xf0;
                #        MCSM1 |= 0x0f;
                #        rf_status = RFST_SRX;
                #
                #        startRX();
                #    }
                #}
                #RFST_SRX = 0x02
                temp = self.readreg(MCSM1) & 0xf0
                self.writereg(MCSM1, temp | 0x0f)
            elif rfmode == RFST_STX:
                #void TxMode(void)
                #{
                #    if (rf_status != RFST_STX)
                #    {
                #        MCSM1 &= 0xf0;
                #        MCSM1 |= 0x0a;
                #
                #        rf_status = RFST_STX;
                #        RFTX;
                #    }
                #}
                #RFST_STX = 0x03
                temp = self.readreg(MCSM1) & 0xf0
                self.writereg(MCSM1, temp | 0x0a)
            elif rfmode == RFST_SIDLE:
                #// enter IDLE mode  (this is significant!  don't do lightly or quickly!)
                #void IdleMode(void)
                #{
                #    if (rf_status != RFST_SIDLE)
                #    {
                #        {
                #            MCSM1 &= 0xf0;
                #            RFIM &= ~RFIF_IRQ_DONE;
                #            RFOFF;
                #
                ##ifdef RFDMA
                #            DMAARM |= (0x80 | DMAARM0);                 // ABORT anything on DMA 0
                #            DMAIRQ &= ~1;
                ##endif
                #
                #            S1CON &= ~(S1CON_RFIF_0|S1CON_RFIF_1);  // clear RFIF interrupts
                #            RFIF &= ~RFIF_IRQ_DONE;
                #        }
                #        rf_status = RFST_SIDLE;
                #        // FIXME: make this also adjust radio register settings for "return to" state?
                #    }
                #}
                #RFST_SIDLE = 0x04
                temp = self.readreg(MCSM1) & 0xf0
                self.writereg(MCSM1, temp)
            #RFST_SNOP                      = 0x05

        else:
            print("Unhandled cmd: {} buf: {}".format(cmd, buf.encode("hex")))
            raise("Unhandled cmd: {} buf: {}".format(cmd, buf.encode("hex")))
        return None, datetime.now() # self.recv(app, cmd, wait)


    def reprDebugCodes(self, timeout=100):
        codes = self.getDebugCodes(timeout)
        if (codes != None and len(codes) == 2):
            rc1 = LCS.get(codes[0])
            rc2 = LCES.get(codes[0])
            return 'last position: %s\nlast error: %s' % (rc1, rc2)
        return codes

    def getDebugCodes(self, timeout=100):
        '''
        this function uses EP0 (not the normal USB EP5) to check the last state of the dongle.
        this only works if the dongle isn't in a hard-loop or some other corrupted state
        that neglects usbprocessing.

        two values are returned.  
        the first value is lastCode[0] and represents standard tracking messages (we were <here>)
        the second value is lastCode[1] and represents exception information (writing OUT while buffer in use!)

        messages LC_* and LCE_* (respectively) are defined in both global.h and rflib.chipcon_usb
        '''
        x = self._recvEP0(request=EP0_CMD_GET_DEBUG_CODES, timeout=timeout)
        if (x != None and len(x)==2):
            return struct.unpack("BB", x)
        else:
            return x

    def clearDebugCodes(self):
        retval = self.send(APP_SYSTEM, SYS_CMD_CLEAR_CODES, "  ", 1000)
        return LCES.get(retval)

    def ep0Ping(self, count=10):
        good=0
        bad=0
        for x in range(count):
            #r = self._recvEP0(3, 10)
            try:
                #XXX: r = self._recvEP0(request=2, value=count, length=count, timeout=DEFAULT_SPI_TIMEOUT)
                print("PING: %d bytes received: %s"%(len(r), repr(r)))
            except ChipconUsbTimeoutException as e:
                r = None
                print("Ping Failed.",e)
            if r==None:
                bad+=1
            else:
                good+=1
        return (good,bad)

    def debug(self, delay=1):
        while True:
            """
            try:
                print >>sys.stderr, ("DONGLE RESPONDING:  mode :%x, last error# %d"%(self.getDebugCodes()))
            except:
                pass
            print >>sys.stderr,('recv_queue:\t\t (%d bytes) "%s"'%(len(self.recv_queue),repr(self.recv_queue)[:len(self.recv_queue)%39+20]))
            print >>sys.stderr,('trash:     \t\t (%d bytes) "%s"'%(len(self.trash),repr(self.trash)[:len(self.trash)%39+20]))
            print >>sys.stderr,('recv_mbox  \t\t (%d keys)  "%s"'%(len(self.recv_mbox),repr(self.recv_mbox)[:len(repr(self.recv_mbox))%79]))
            for x in self.recv_mbox.keys():
                print >>sys.stderr,('    recv_mbox   %d\t (%d records)  "%s"'%(x,len(self.recv_mbox[x]),repr(self.recv_mbox[x])[:len(repr(self.recv_mbox[x]))%79]))
                """
            print(self.reprRadioState())
            print(self.reprClientState())

            x,y,z = select.select([sys.stdin],[],[], delay)
            if sys.stdin in x:
                sys.stdin.read(1)
                break

    def getPartNum(self):
        try:
            r = self.send(APP_SYSTEM, SYS_CMD_PARTNUM, "", 10000)
            r,rt = r
        except ChipconUsbTimeoutException as e:
            r = None
            print("SETUP Failed.",e)

        return ord(r)

    def getVersion(self):
        try:
            r = self.send(APP_SYSTEM, SYS_CMD_VERSION, "", 10000)
            r,rt = r
        except ChipconUsbTimeoutException as e:
            r = None
            print("SETUP Failed.",e)

        return ord(r)


    def ping(self, count=10, buf="ABCDEFGHIJKLMNOPQRSTUVWXYZ", wait=DEFAULT_SPI_TIMEOUT, silent=False):
        version = self.getVersion()
        good=0
        bad=0
        start = time.time()
        if (version == 0x14):
            good=count
        stop = time.time()
        return (good,bad,stop-start)

    def bootloader(self):
        '''
        switch to bootloader mode. based on Fergus Noble's CC-Bootloader (https://github.com/fnoble/CC-Bootloader)
        this allows the firmware to be updated via USB instead of goodfet/ccdebugger
        '''
        try:
            self._bootloader = True
            r = self.send(APP_SYSTEM, SYS_CMD_BOOTLOADER, "", wait=1)
        except ChipconUsbTimeoutException:
            pass
        
    def RESET(self):
        try:
            r = self.send(APP_SYSTEM, SYS_CMD_RESET, "RESET_NOW\x00")
        except ChipconUsbTimeoutException:
            pass
        
    def peek(self, addr, bytecount=1):
        print("peek: bytecount {} addr {}".format(bytecount, addr))
        r, t = self.send(APP_SYSTEM, SYS_CMD_PEEK, struct.pack("<HB", bytecount, addr))
        return r

    def poke(self, addr, data):
        r, t = self.send(APP_SYSTEM, SYS_CMD_POKE, struct.pack("<B", addr) + data)
        return r
    
    def pokeReg(self, addr, data):
        r, t = self.send(APP_SYSTEM, SYS_CMD_POKE_REG, struct.pack("<B", addr) + data)
        return r

    def getBuildInfo(self):
        r, t = self.send(APP_SYSTEM, SYS_CMD_BUILDTYPE, '')
        return r
            
    def getCompilerInfo(self):
        r, t = self.send(APP_SYSTEM, SYS_CMD_COMPILER, '')
        return r
            
    def getInterruptRegisters(self):
        regs = {}
        # IEN0,1,2
        regs['IEN0'] = self.peek(IEN0,1)
        regs['IEN1'] = self.peek(IEN1,1)
        regs['IEN2'] = self.peek(IEN2,1)
        # TCON
        regs['TCON'] = self.peek(TCON,1)
        # S0CON
        regs['S0CON'] = self.peek(S0CON,1)
        # IRCON
        regs['IRCON'] = self.peek(IRCON,1)
        # IRCON2
        regs['IRCON2'] = self.peek(IRCON2,1)
        # S1CON
        regs['S1CON'] = self.peek(S1CON,1)
        # RFIF
        regs['RFIF'] = self.peek(RFIF,1)
        # DMAIE
        regs['DMAIE'] = self.peek(DMAIE,1)
        # DMAIF
        regs['DMAIF'] = self.peek(DMAIF,1)
        # DMAIRQ
        regs['DMAIRQ'] = self.peek(DMAIRQ,1)
        return regs

    def reprHardwareConfig(self):
        output= []

        hardware = self.getBuildInfo()
        output.append("Dongle:              %s" % hardware.split(' ')[0])
        try:
            output.append("Firmware rev:        %s" % hardware.split('r')[1])
        except:
            output.append("Firmware rev:        Not found! Update needed!")
        try:
            compiler = self.getCompilerInfo()
            output.append("Compiler:            %s" % compiler)
        except:
            output.append("Compiler:            Not found! Update needed!")
        # see if we have a bootloader by loooking for it's recognition semaphores
        # in SFR I2SCLKF0 & I2SCLKF1
        if(self.peek(0xDF46,1) == '\xF0' and self.peek(0xDF47,1) == '\x0D'):
            output.append("Bootloader:          CC-Bootloader")
        else:
            output.append("Bootloader:          Not installed")
        return "\n".join(output)

    def reprSoftwareConfig(self):
        output= []

        output.append("rflib rev:           %s" % RFLIB_VERSION)
        return "\n".join(output)

    def printClientState(self, width=120):
        print(self.reprClientState(width))

    def reprClientState(self, width=120):
        output = ["="*width]
        output.append('     client thread cycles:      %d/%d' % (self.recv_threadcounter,self.send_threadcounter))
        output.append('     client errored cycles:     %d' % self._usberrorcnt)
        output.append('     recv_queue:                (%d bytes) %s'%(len(self.recv_queue),repr(self.recv_queue)[:width-42]))
        output.append('     trash:                     (%d blobs) "%s"'%(len(self.trash),repr(self.trash)[:width-44]))
        output.append('     recv_mbox                  (%d keys)  "%s"'%(len(self.recv_mbox),repr([hex(x) for x in list(self.recv_mbox.keys())])[:width-44]))
        for app in list(self.recv_mbox.keys()):
            appbox = self.recv_mbox[app]
            output.append('       app 0x%x (%d records)'%(app,len(appbox)))
            for cmd in list(appbox.keys()):
                output.append('             [0x%x]    (%d frames)  "%s"'%(cmd, len(appbox[cmd]), repr(appbox[cmd])[:width-36]))
            output.append('')
        return "\n".join(output)



def unittest(self, mhz=8):
    print("\nTesting SPI ping()")
    self.ping(3)
    
    print("\nTesting SPI ep0Ping()")
    self.ep0Ping()
    
    print("\nTesting SPI enumeration")
    print("getString(0,100): %s" % repr(self._do.getString(0,100)))
    
    print("\nTesting SPI EP MAX_PACKET_SIZE handling (ep0Peek(0xf000, 100))")
    #print(repr(self.ep0Peek(0xf000, 100)))

    print("\nTesting SPI EP MAX_PACKET_SIZE handling (peek(0xf000, 300))")
    #print(repr(self.peek(0xf000, 400)))

    print("\nTesting SPI poke/peek")
    #data = "".join([correctbytes(c) for c in range(120)])
    #where = 0xf300
    #self.poke(where, data)
    #ndata = self.peek(where, len(data))
    #if ndata != data:
    #    print(" *FAILED*\n '%s'\n '%s'" % (data.encode("hex"), ndata.encode("hex")))
    #    raise Exception(" *FAILED*\n '%s'\n '%s'" % (data.encode("hex"), ndata.encode("hex")))
    #else:
    #    print("  passed  '%s'" % (ndata.encode("hex")))


if __name__ == "__main__":
    idx = 0
    if len(sys.argv) > 1:
        idx = int(sys.argv.pop())
    d = SPIDongle(idx=idx, debug=False)


