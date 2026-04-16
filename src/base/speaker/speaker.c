/*
 * Speaker emulation code, file speaker.c
 *
 * (C) 1997 under GPL or LGPL, Eric Biederman <ebiederm+eric@nwpt.net>
 *
 * DANG_BEGIN_MODULE
 *
 * REMARK
 *
 * The pc-speaker emulator for Dosemu.
 *
 * This file contains functions to make a pc speaker beep for dosemu.
 *
 * Actuall emulation is done in src/base/dev/misc/timers.c in do_sound.
 *
 * Currently emulation is only done when the new keyboard is enabled but with a
 * little extra work it should be possible to enable it for the old keyboard
 * code if necessary.
 *
 * For parts of dosemu that want to beep the pc-speaker (say the video bios)
 * #include "speaker.h"
 * Use 'speaker_on(ms, period)'
 * to turn the pc-speaker on for 'ms' milliseconds with period 'period'.
 * The function returns immediately.
 *
 * Use 'speaker_off()'
 * To turn the pc-speaker definentily off.  This is mostly useful when exiting
 * the program to ensure you aren't killy someones ears :)
 *
 * 'speaker_on' always overrides whatever previous speaker sound was previously
 * given.  No mixing happens.
 *
 * For code that wants to implement speaker emulation.  The recommended method
 * is to add a file in src/base/speaker with the necessary code.  Declare it's
 * methods in speaker.h (or somewhere accessible to your code).  And call
 *
 * 'register_speaker(gp, on, off)'
 * when your speaker code is ready to function.
 *
 *  gp may be any void pointer value.
 *
 *  gp is passed as the first argument to the functions arguments 'on'
 *  and 'off' when global functions 'speaker_on' and 'speaker_off' are called.
 *  This allows important state information to be passed to the functions.  And
 *  reduces reliance on global variables.
 *
 * The functions 'on' and 'off' besides the extra parameter are called just as
 * the global functions 'speaker_on' and 'speaker_off' are called respectively.
 *
 * Before the registered function is no longer valid call
 * 'register_speaker(NULL, NULL, NULL)' this will reset the speaker code
 * to it's default speaker functions, which will always work.
 *
 * --EB 20 Sept 1997
 *
 * /REMARK
 * maintainer:
 * Eric W. Biederman <eric@biederman.org>
 * DANG_END_MODULE
 *
 * Changes:	Hans 970926 (at time of patch inclusion)
 *		- Reduced type/prototyping usage to DOSEMU common one ;-)
 *
 */

#include "emu.h"
#include "speaker.h"
#include "port.h"
#include "iodev.h"
#include "timers.h"

/*
 * Speaker info structure.
 * ============================================================================
 */
struct speaker_info {
	void *gp;  /* a general pointer it can hold anything,
		    * it is passed to both speaker_on & speaker_off
		    */
	speaker_on_t on;
	speaker_off_t off;
};

/* flag to avoid turning the speaker off if it is already off */
static int speaker_is_on;

/*
 * Generic speaker emulation
 * =============================================================================
 */
#include "sound/sound.h"
#include <unistd.h>

#define DIV_ROUND_UP(n,d) (((n) + (d) - 1) / (d))
#define PCSPK_BUF_LEN 2470
#define PCSPK_SAMPLE_RATE 44100
#define PCSPK_MAX_FREQ (PCSPK_SAMPLE_RATE >> 1)
#define PCSPK_MIN_COUNT DIV_ROUND_UP(SPEAKER_PERIOD_BASE, PCSPK_MAX_FREQ) // 55

typedef struct {
	int pit_count;
	int samples;
	sndbuf_t sample_buf[PCSPK_BUF_LEN][SNDBUF_CHANS];
} PCSpkState;

static PCSpkState beep;
static int pcm_stream = -1;

/*
 * wave generation function from QEMU: hw/audio/pcspk.c
 */
static inline void generate_samples(PCSpkState *s)
{
	unsigned int i;

	if (s->pit_count) {
		const uint32_t m = PCSPK_SAMPLE_RATE * s->pit_count;
		const uint32_t n = ((uint64_t)SPEAKER_PERIOD_BASE << 32) / m;

		/* multiple of wavelength for gapless looping */
		s->samples = ((PCSPK_BUF_LEN * SPEAKER_PERIOD_BASE / m * m) / (SPEAKER_PERIOD_BASE >> 1) + 1) >> 1;
		for (i = 0; i < s->samples; ++i)
			s->sample_buf[i][0] = (64 & (n * i >> 25)) - 32;
	} else {
		s->samples = PCSPK_BUF_LEN;
		for (i = 0; i < PCSPK_BUF_LEN; ++i)
			s->sample_buf[i][0] = 128; /* silence */
	}
}

static void gen_speaker_keep_on(void)
{
	/* we need to keep feeding the sound midlayer to keep the speaker on */
	if (pcm_stream == -1 || beep.samples == 0) return;

	if (pcm_get_stream_time(pcm_stream) < GETusTIME(0) + 1000000ULL * beep.samples / PCSPK_SAMPLE_RATE)
		pcm_write_interleaved(beep.sample_buf, beep.samples, PCSPK_SAMPLE_RATE, PCM_FORMAT_U8,
				      1, pcm_stream);
}

static void gen_speaker_on(void *gp, unsigned ms, unsigned short period)
{
	if (pcm_stream == -1) {
		sigalrm_register_handler(gen_speaker_keep_on);
		pcm_stream = pcm_allocate_stream(1, "PC-SPEAKER", 0);
	}

	if (beep.samples)
		pcm_flush(pcm_stream);

	/* avoid frequencies that are not reproducible with sample rate */
	if (period < PCSPK_MIN_COUNT)
		period = 0;

	beep.pit_count = period;
	generate_samples(&beep);

	// mix our beep against the PCM stream
	pcm_write_interleaved(beep.sample_buf, beep.samples, PCSPK_SAMPLE_RATE, PCM_FORMAT_U8,
			      1, pcm_stream);
}

static void gen_speaker_off(void *gp)
{
	if (pcm_stream != -1)
		pcm_flush(pcm_stream);
	beep.samples = 0;
}

static struct speaker_info gen_speaker =
{ NULL, gen_speaker_on, gen_speaker_off };

/*
 * Speaker Emulation Control
 * =============================================================================
 */


static struct speaker_info speaker =
{ NULL, gen_speaker_on, gen_speaker_off};

void register_speaker(void *gp,
			     speaker_on_t speaker_on,
			     speaker_off_t speaker_off)
{
	if (speaker_on && speaker_off) {
		speaker.gp = gp;
		speaker.on = speaker_on;
		speaker.off = speaker_off;
	} else {
		speaker = gen_speaker;
	}
}

/* this does the EMULATED mode speaker emulation */
void speaker_on(unsigned ms, unsigned short period)
{
	if (config.speaker == SPKR_OFF)
		return;
	i_printf("SPEAKER: on, period=%d\n", period);
	speaker_is_on = 1;
	if (!speaker.on) {
		speaker = gen_speaker;
	}
	speaker.on(speaker.gp, ms, period);
}

void speaker_off(void)
{
	if (!speaker_is_on)
		return;
	i_printf("SPEAKER: sound OFF!\n");
	if (!speaker.off) {
		speaker = gen_speaker;
	}
	speaker.off(speaker.gp);
	speaker_is_on = 0;
}

static int saved_port_val;
void speaker_pause (void)
{
	switch (config.speaker)
	{
	case SPKR_NATIVE:
		saved_port_val = port_inb (0x61);
		std_port_outb (0x61, saved_port_val & 0xFC);	/* clear timer & speaker bits */
		break;
	case SPKR_EMULATED:
	case SPKR_GENERATED:
		speaker_off ();
		break;
	case SPKR_OFF:
		break;
	}
}

void speaker_resume (void)
{
	switch (config.speaker)
	{
	case SPKR_NATIVE:
		std_port_outb (0x61, saved_port_val);	/* restore timer & speaker bits */
		break;
	case SPKR_EMULATED:
	case SPKR_GENERATED:
//		do_sound(pit[2].write_latch & 0xffff);
		break;
	case SPKR_OFF:
		break;
	}
}
