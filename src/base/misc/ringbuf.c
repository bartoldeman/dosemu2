/*
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

/*
 * Purpose: ring buffer API.
 *
 * Author: Stas Sergeev <stsp@users.sourceforge.net>
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "ringbuf.h"

void rng_init(struct rng_s *rng, size_t objnum, size_t objsize)
{
  rng->buffer = calloc(objnum, objsize);
  rng->objnum = objnum;
  rng->objsize = objsize;
  rng->tail = rng->objcnt = 0;
}

int rng_destroy(struct rng_s *rng)
{
  int ret = rng->objcnt;
  free(rng->buffer);
  rng->objcnt = 0;
  return ret;
}

int rng_get(struct rng_s *rng, void *buf)
{
  if (!rng->objcnt)
    return 0;
  if (buf)
    memcpy(buf, rng->buffer + rng->tail, rng->objsize);
  rng->tail += rng->objsize;
  rng->tail %= rng->objsize * rng->objnum;
  rng->objcnt--;
  return 1;
}

int rng_peek(struct rng_s *rng, int idx, void *buf)
{
  int obj_pos;
  if (rng->objcnt <= idx)
    return 0;
  obj_pos = (rng->tail + idx * rng->objsize) % (rng->objnum * rng->objsize);
  assert(buf);
  memcpy(buf, rng->buffer + obj_pos, rng->objsize);
  return 1;
}

int rng_put(struct rng_s *rng, void *obj)
{
  int head_pos, ret = 1;
  head_pos = (rng->tail + rng->objcnt * rng->objsize) % (rng->objnum * rng->objsize);
  assert(head_pos <= (rng->objnum - 1) * rng->objsize);
  memcpy(rng->buffer + head_pos, obj, rng->objsize);
  rng->objcnt++;
  if (rng->objcnt > rng->objnum) {
    rng_get(rng, NULL);
    ret = 0;
  }
  assert(rng->objcnt <= rng->objnum);
  return ret;
}

int rng_put_const(struct rng_s *rng, int value)
{
  assert(rng->objsize <= sizeof(value));
  return rng_put(rng, &value);
}

int rng_poke(struct rng_s *rng, int idx, void *buf)
{
  int obj_pos;
  if (rng->objcnt <= idx)
    return 0;
  obj_pos = (rng->tail + idx * rng->objsize) % (rng->objnum * rng->objsize);
  memcpy(rng->buffer + obj_pos, buf, rng->objsize);
  return 1;
}

int rng_add(struct rng_s *rng, int num, void *buf)
{
  int i, ret = 0;
  for (i = 0; i < num; i++)
    ret += rng_put(rng, (unsigned char *)buf + i * rng->objsize);
  return ret;
}

int rng_remove(struct rng_s *rng, int num, void *buf)
{
  int i, ret = 0;
  for (i = 0; i < num; i++)
    ret += rng_get(rng, buf ? (unsigned char *)buf + i * rng->objsize : NULL);
  return ret;
}

int rng_count(struct rng_s *rng)
{
  return rng->objcnt;
}

void rng_clear(struct rng_s *rng)
{
  rng->objcnt = 0;
}
